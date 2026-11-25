/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Weighted cost bounds through stateless oracle substitution

Each source query is implemented by an actual target-oracle program. When every completed run of
that implementation fits the source query's charge, substitution preserves the source program's
weighted bound. Costs may be vectors or any ordered additive commutative monoid. The route is
stateless: it does not thread additional handler-local `StateT` state between calls. The target
oracle may be interpreted in a stateful runtime separately. Stateful query-count simulation is
treated separately in `QueryBound.Simulation`; this module does not supply a stateful weighted-cost
refinement theorem.

The support refinement retains the returned value and compares the charges of the two runs. It
does not identify their probability distributions. Bounds concern completed runs only: an
implementation with no completed run satisfies every such bound. Availability and termination
therefore require separate hypotheses where those properties are needed.

`WorstCaseCostBound.simulateQ` reads only completed paths, so the two query indices, the target
responses and the cost carrier have independent universes. The source responses share the
results' universe, because `simulateQ` folds into a monad over the response universe. The support
lemmas run `costDist` on both sides, so there the responses, the results and the costs share one
universe.
-/

public section

open OracleSpec OracleComp

universe uι uκ v v' w u

section Support

variable {ι : Type uι} {κ : Type uκ} {α ω : Type u} {source : OracleSpec.{uι, u} ι}
  {target : OracleSpec.{uκ, u} κ} [AddCommMonoid ω]

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

/-- Every completed substituted run has a source run with the same result and at least its charge.
The source query charge must bound the entire implementing program, including repeated queries.
This is PolyFun's completed-path refinement `PFunctor.FreeM.Path.exists_path_liftM` read through
`support_costDist_eq_range_path`. -/
theorem mem_support_costDist_simulateQ [Preorder ω] [IsOrderedAddMonoid ω]
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source α)
    (sourceCost : CostModel source ω) (targetCost : CostModel target ω)
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query))
    (result : α × Multiplicative ω)
    (member : result ∈ support (costDist (simulateQ route program) targetCost)) :
    ∃ charge : ω, (result.1, Multiplicative.ofAdd charge) ∈ support (costDist program sourceCost) ∧
      Multiplicative.toAdd result.2 ≤ charge := by
  rw [support_costDist_eq_range_path] at member
  obtain ⟨q, rfl⟩ := member
  obtain ⟨p, hout, hle⟩ := PFunctor.FreeM.Path.exists_path_liftM route
    (fun query => (worstCaseCostBound_iff_forall_charge_le _ _ _).1 (hstep query)) program q
  refine ⟨_, ?_, hle⟩
  rw [support_costDist_eq_range_path]
  exact ⟨p, Prod.ext hout rfl⟩

end Support

/-- A source weighted bound transfers through the same stateless handler programs whose costs
are bounded. The charge of each complete handler call includes all its target queries. This is
PolyFun's completed-path transfer `PFunctor.FreeM.Path.charge_liftM_le_of_forall`. -/
theorem WorstCaseCostBound.simulateQ {ι : Type uι} {κ : Type uκ} {α : Type v} {ω : Type w}
    {source : OracleSpec.{uι, v} ι} {target : OracleSpec.{uκ, v'} κ}
    [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω] {program : OracleComp source α}
    {sourceCost : CostModel source ω} {targetCost : CostModel target ω} {budget : ω}
    (hprogram : WorstCaseCostBound program sourceCost budget)
    (route : QueryImpl source (OracleComp target))
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query)) :
    WorstCaseCostBound (simulateQ route program) targetCost budget := by
  rw [worstCaseCostBound_iff_forall_charge_le] at hprogram ⊢
  exact PFunctor.FreeM.Path.charge_liftM_le_of_forall route
    (fun query => (worstCaseCostBound_iff_forall_charge_le _ _ _).1 (hstep query)) hprogram

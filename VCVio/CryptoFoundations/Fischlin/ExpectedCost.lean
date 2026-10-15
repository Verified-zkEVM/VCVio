/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.CostAccounting
public import VCVio.CryptoFoundations.Fischlin.Completeness
import all VCVio.CryptoFoundations.Fischlin.CostAccounting
import all VCVio.CryptoFoundations.Fischlin.Completeness
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Expected cost of Fischlin's zero-stopping search

The query counter instruments the actual search with the standard additive writer.
Fresh challenges give independent uniform hashes until the first zero, with truncation
at the end of the challenge list. Repetitions use distinct random-oracle input tags.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (ρ b : ℕ)
  (M : Type) [DecidableEq M]

/-- The actual search's output, additive query counter, and final random-oracle cache. -/
@[expose]
def searchCostRun (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    ProbComp ((Option (Chal × Resp) × Multiplicative ℕ) ×
      (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :=
  ((HasQuery.Program.withUnitCost
    (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (AddWriterT ℕ (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp))] =>
      fischlinSearchAux σ pk sk sc msg comList i cs best)
    (randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M))).run).run cache

/-- Exhausting the challenge list returns the current best answer and spends no more queries. -/
theorem searchCostRun_nil (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    searchCostRun σ ρ b M pk sk sc msg comList i [] best cache =
      pure ((best.map fun t => (t.1, t.2.1), 1), cache) := by
  simp [searchCostRun, HasQuery.Program.withUnitCost, fischlinSearchAux]

/-- A fresh challenge makes one hash query, stopping at zero and otherwise continuing. -/
theorem searchCostRun_cons (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (c : Chal) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ r, cache ⟨pk, msg, comList, i, c, r⟩ = none) :
    searchCostRun σ ρ b M pk sk sc msg comList i (c :: cs) best cache =
      (do
        let r ← σ.respond pk sk sc c
        let h ← $ᵗ Fin (2 ^ b)
        let cache' := cache.cacheQuery ⟨pk, msg, comList, i, c, r⟩ h
        if h.val = 0 then return ((some (c, r), Multiplicative.ofAdd 1), cache')
        else
          let best' := match best with
            | none => some (c, r, h)
            | some (c', r', h') =>
                if h.val < h'.val then some (c, r, h) else some (c', r', h')
          let z ← searchCostRun σ ρ b M pk sk sc msg comList i cs best' cache'
          return ((z.1.1, Multiplicative.ofAdd (1 + z.1.2.toAdd)), z.2)) := by
  simp only [searchCostRun, HasQuery.Program.withUnitCost, fischlinSearchAux,
    HasQuery.Program.withAddCost_bind, HasQuery.Program.withAddCost_query]
  simp only [HasQuery.Program.withAddCost,
    monadLift, MonadLift.monadLift, map_eq_bind_pure_comp, AddWriterT.addTell,
    QueryImpl.withCaching_apply, liftM, uniformSampleImpl, Fin.val_eq_zero_iff,
    Fin.val_fin_lt, WriterT.run_bind, WriterT.run_mk, WriterT.run_tell, bind_assoc,
    Function.comp_apply, pure_bind, one_mul, Prod.mk.eta, bind_pure_comp,
    StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, hfresh,
    StateT.run_modifyGet, ofAdd_add, ofAdd_toAdd]
  apply bind_congr
  intro r
  apply bind_congr
  intro h
  by_cases hh : h = 0
  · simp [hh]
  · simp [hh]
    rfl

/-- A cached challenge still costs one hash call, while preserving the cached answer and state. -/
theorem searchCostRun_cons_cached (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (c : Chal) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (cached : Resp → Fin (2 ^ b))
    (hcache : ∀ r, cache ⟨pk, msg, comList, i, c, r⟩ = some (cached r)) :
    searchCostRun σ ρ b M pk sk sc msg comList i (c :: cs) best cache =
      (do
        let r ← σ.respond pk sk sc c
        let h := cached r
        if h.val = 0 then return ((some (c, r), Multiplicative.ofAdd 1), cache)
        else
          let best' := match best with
            | none => some (c, r, h)
            | some (c', r', h') =>
                if h.val < h'.val then some (c, r, h) else some (c', r', h')
          let z ← searchCostRun σ ρ b M pk sk sc msg comList i cs best' cache
          return ((z.1.1, Multiplicative.ofAdd (1 + z.1.2.toAdd)), z.2)) := by
  simp only [searchCostRun, HasQuery.Program.withUnitCost, fischlinSearchAux,
    HasQuery.Program.withAddCost_bind, HasQuery.Program.withAddCost_query]
  simp only [HasQuery.Program.withAddCost,
    monadLift, MonadLift.monadLift, map_eq_bind_pure_comp, AddWriterT.addTell,
    QueryImpl.withCaching_apply, liftM, Fin.val_eq_zero_iff,
    Fin.val_fin_lt, WriterT.run_bind, WriterT.run_mk, WriterT.run_tell, bind_assoc,
    Function.comp_apply, pure_bind, one_mul, Prod.mk.eta, bind_pure_comp,
    StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, hcache,
    ofAdd_add, ofAdd_toAdd]
  apply bind_congr
  intro r
  by_cases hh : cached r = 0
  · simp [hh]
  · simp [hh]
    rfl

/-- The distribution of the actual additive writer's query count. -/
@[expose]
def searchQueryCount (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : ProbComp ℕ :=
  (fun z => z.1.2.toAdd) <$> searchCostRun σ ρ b M pk sk sc msg comList i cs best cache

/-- Expected queries in the actual search, with an explicit initial cache. -/
@[expose]
noncomputable def searchExpectedQueries
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit) (i : Fin ρ)
    (cs : List Chal) (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : ℝ≥0∞ :=
  ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[searchQueryCount σ ρ b M pk sk sc msg comList i cs best cache]

private theorem searchQueryCount_cons (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (c : Chal) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ r, cache ⟨pk, msg, comList, i, c, r⟩ = none) :
    searchQueryCount σ ρ b M pk sk sc msg comList i (c :: cs) best cache =
      (do
        let r ← σ.respond pk sk sc c
        let h ← $ᵗ Fin (2 ^ b)
        let cache' := cache.cacheQuery ⟨pk, msg, comList, i, c, r⟩ h
        if h.val = 0 then return 1
        else
          let best' := match best with
            | none => some (c, r, h)
            | some (c', r', h') =>
                if h.val < h'.val then some (c, r, h) else some (c', r', h')
          (fun n => 1 + n) <$>
            searchQueryCount σ ρ b M pk sk sc msg comList i cs best' cache') := by
  simp only [searchQueryCount, searchCostRun_cons σ ρ b M pk sk sc msg comList i c cs
    best cache hfresh, map_bind]
  apply bind_congr
  intro r
  apply bind_congr
  intro h
  by_cases hh : h.val = 0 <;> simp [hh]

/-- The expected queries as the expectation of the query count. -/
theorem searchExpectedQueries_eq_wp (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (cs : List Chal)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    searchExpectedQueries σ ρ b M pk sk sc msg comList i cs best cache =
      𝔼{let n ← searchQueryCount σ ρ b M pk sk sc msg comList i cs best cache}[(n : ℝ≥0∞)] :=
  (ExpectationWP.wp_eq_lintegral _ _ Measurable.of_discrete).symm

private theorem uniform_nonzero_mass :
    𝒟[$ᵗ Fin (2 ^ b)] {h | h.val ≠ 0} = 1 - (2 ^ b : ℝ≥0∞)⁻¹ := by
  have : NeZero (2 ^ b) := ⟨(Nat.two_pow_pos b).ne'⟩
  have hset : {h : Fin (2 ^ b) | h.val ≠ 0} = ({0} : Set (Fin (2 ^ b)))ᶜ := by
    ext h
    simp
  rw [hset, SampleableType.evalDist_uniformSample, measure_compl (measurableSet_singleton 0)]
  · simp
  · exact measure_ne_top _ _

/-- A fresh hash stops at zero and otherwise continues: the expectation of the two branches. -/
private theorem wp_zero_continue (t : ℝ≥0∞) :
    𝔼{let h ← $ᵗ Fin (2 ^ b)}[if h.val = 0 then 1 else 1 + t] =
      1 + (1 - (2 ^ b : ℝ≥0∞)⁻¹) * t := by
  rw [ExpectationWP.wp_eq_lintegral _ _ Measurable.of_discrete]
  have hf : (fun h : Fin (2 ^ b) => if h.val = 0 then (1 : ℝ≥0∞) else 1 + t) =
      (fun h => 1 + {h : Fin (2 ^ b) | h.val ≠ 0}.indicator (fun _ => t) h) := by
    funext h
    simp only [Set.indicator, Set.mem_ofPred_eq, ne_eq]
    split_ifs <;> simp_all
  rw [hf, lintegral_add_left measurable_const, lintegral_indicator MeasurableSet.of_discrete]
  simp only [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one,
    Measure.restrict_apply_univ,
    uniform_nonzero_mass, mul_comm t]

/-- Exact expected queries of the instrumented search. Every remaining challenge must be fresh
for every possible response, and the challenge list must have no duplicates. -/
theorem searchExpectedQueries_eq_sum (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M)
    (comList : List Commit) (i : Fin ρ) (cs : List Chal) (hcs : cs.Nodup)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ c ∈ cs, ∀ r, cache ⟨pk, msg, comList, i, c, r⟩ = none) :
    searchExpectedQueries σ ρ b M pk sk sc msg comList i cs best cache =
      ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
  classical
  let : MeasurableSpace Resp := ⊤
  induction cs generalizing best cache with
  | nil =>
    simp [searchExpectedQueries, searchQueryCount, searchCostRun_nil]
  | cons c cs ih =>
    have hfresh' (r : Resp) (h : Fin (2 ^ b)) : ∀ c' ∈ cs, ∀ r',
        (cache.cacheQuery ⟨pk, msg, comList, i, c, r⟩ h)
          ⟨pk, msg, comList, i, c', r'⟩ = none := by
      intro c' hc' r'
      have hne : (⟨pk, msg, comList, i, c', r'⟩ : FischlinROInput Stmt Commit Chal Resp ρ M)
          ≠ ⟨pk, msg, comList, i, c, r⟩ := by
        intro heq
        have hcc := congrArg FischlinROInput.chal heq
        change c' = c at hcc
        exact (List.nodup_cons.mp hcs).1 (hcc ▸ hc')
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hfresh c' (List.mem_cons_of_mem c hc') r'
    have ih' : ∀ (best' : Option (Chal × Resp × Fin (2 ^ b))) (r : Resp) (h : Fin (2 ^ b)),
        𝔼{let n ← (searchQueryCount σ ρ b M pk sk sc msg comList i cs best'
          (cache.cacheQuery ⟨pk, msg, comList, i, c, r⟩ h) : ProbComp ℕ)}[(n : ℝ≥0∞)] =
          ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j :=
      fun best' r h => (searchExpectedQueries_eq_wp σ ρ b M pk sk sc msg comList i cs best'
        _).symm.trans (ih (List.nodup_cons.mp hcs).2 best' _ (hfresh' r h))
    rw [searchExpectedQueries_eq_wp, searchQueryCount_cons σ ρ b M pk sk sc msg comList i c cs
      best cache (fun r => hfresh c (by simp) r)]
    simp only [expect_norm, Nat.cast_add, Nat.cast_one, ExpectationWP.wp_add,
      ExpectationWP.wp_const_of_oracle, ih', wp_zero_continue b, List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, ← Finset.mul_sum, pow_succ', add_comm]

/-- The finite geometric sum has the usual closed form, including a one-point hash range. -/
theorem geometricSearchSum_eq (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j =
      (2 ^ b : ℝ≥0∞) * (1 - (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ n) := by
  have hpos : (0 : ℝ≥0) < 2 ^ b := pow_pos (by norm_num) _
  have hinv : (2 ^ b : ℝ≥0)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  have h := geom_sum_mul_of_le_one (tsub_le_self : 1 - (2 ^ b : ℝ≥0)⁻¹ ≤ 1) n
  rw [tsub_tsub_cancel_of_le hinv] at h
  have hclosed : (∑ j ∈ Finset.range n, (1 - (2 ^ b : ℝ≥0)⁻¹) ^ j) =
      (2 ^ b : ℝ≥0) * (1 - (1 - (2 ^ b : ℝ≥0)⁻¹) ^ n) := by
    rw [← h]
    rw [mul_left_comm, mul_inv_cancel₀ hpos.ne', mul_one]
  have hcast := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hclosed
  simpa only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_sub, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_one, ENNReal.coe_ofNat, ENNReal.coe_inv hpos.ne'] using hcast

end Fischlin

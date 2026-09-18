/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Fischlin.ExpectedCost

/-!
# Expected queries across the actual Fischlin prover

Repetition tags preserve freshness of the searches still to run. The standard writer counts
the sequential `Fin.mOfFn` execution; formatting a search result into a proof has no query cost.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (ρ b : ℕ)
  (M : Type) [DecidableEq M]

private theorem fresh_tail (pk : Stmt) (msg : M) (comList : List Commit)
    (i : Fin ρ) (c : Chal) (cs : List Chal) (hcs : (c :: cs).Nodup)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ c' ∈ c :: cs, ∀ r', cache ⟨pk, msg, comList, i, c', r'⟩ = none)
    (r : Resp) (h : Fin (2 ^ b)) : ∀ c' ∈ cs, ∀ r',
    (cache.cacheQuery ⟨pk, msg, comList, i, c, r⟩ h)
      ⟨pk, msg, comList, i, c', r'⟩ = none := by
  intro c' hc' r'
  have hne : (⟨pk, msg, comList, i, c', r'⟩ : FischlinROInput Stmt Commit Chal Resp ρ M)
      ≠ ⟨pk, msg, comList, i, c, r⟩ := by
    intro heq
    have hcc : c' = c := congrArg FischlinROInput.chal heq
    exact (List.nodup_cons.mp hcs).1 (hcc ▸ hc')
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hfresh c' (List.mem_cons_of_mem c hc') r'

private theorem searchCostRun_preserves_offrep
    (pk : Stmt) (sk : Wit) (sc : PrvState) (msg : M) (comList : List Commit)
    (i : Fin ρ) (cs : List Chal) (hcs : cs.Nodup)
    (best : Option (Chal × Resp × Fin (2 ^ b)))
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ c ∈ cs, ∀ r, cache ⟨pk, msg, comList, i, c, r⟩ = none)
    {z : (Option (Chal × Resp) × Multiplicative ℕ) ×
      (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache}
    (hz : z ∈ support (searchCostRun σ ρ b M pk sk sc msg comList i cs best cache))
    (input : FischlinROInput Stmt Commit Chal Resp ρ M) (hi : input.rep ≠ i) :
    z.2 input = cache input := by
  induction cs generalizing best cache z with
  | nil =>
    rw [searchCostRun_nil, mem_support_pure_iff] at hz
    subst z
    rfl
  | cons c cs ih =>
    rw [searchCostRun_cons σ ρ b M pk sk sc msg comList i c cs best cache
      (fun r => hfresh c (by simp) r), mem_support_bind_iff] at hz
    obtain ⟨r, _, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨h, _, hz⟩ := hz
    have hne : input ≠ ⟨pk, msg, comList, i, c, r⟩ :=
      fun heq => hi (congrArg FischlinROInput.rep heq)
    by_cases hh : h.val = 0
    · simp only [hh, ite_true, mem_support_pure_iff] at hz
      subst z
      exact QueryCache.cacheQuery_of_ne cache h hne
    · simp only [hh, ite_false, mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact (ih (List.nodup_cons.mp hcs).2 _ _
        (fresh_tail ρ b M pk msg comList i c cs hcs cache hfresh r h) hz').trans
          (QueryCache.cacheQuery_of_ne cache h hne)

/-- The actual sequential searches, with arbitrary query-free formatting of their outputs. -/
@[expose]
def searchesCostRun {T : Type} (n : ℕ) (e : Fin n → Fin ρ)
    (pk : Stmt) (sk : Wit) (sc : Fin n → PrvState) (msg : M) (comList : List Commit)
    (cs : List Chal) (format : Fin n → Option (Chal × Resp) → T)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    ProbComp (((Fin n → T) × Multiplicative ℕ) ×
      (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :=
  ((HasQuery.Program.withUnitCost
    (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (AddWriterT ℕ (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp))] =>
      Fin.mOfFn n fun j => format j <$>
        fischlinSearchAux (b := b) σ pk sk (sc j) msg comList (e j) cs none)
    (randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M))).run).run cache

/-- The query-count marginal of the actual sequential search execution. -/
@[expose]
def searchesQueryCount {T : Type} (n : ℕ) (e : Fin n → Fin ρ)
    (pk : Stmt) (sk : Wit) (sc : Fin n → PrvState) (msg : M) (comList : List Commit)
    (cs : List Chal) (format : Fin n → Option (Chal × Resp) → T)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : ProbComp ℕ :=
  (fun z => z.1.2.toAdd) <$>
    searchesCostRun σ ρ b M n e pk sk sc msg comList cs format cache

private theorem searchesQueryCount_succ {T : Type} (n : ℕ) (e : Fin (n + 1) → Fin ρ)
    (pk : Stmt) (sk : Wit) (sc : Fin (n + 1) → PrvState) (msg : M) (comList : List Commit)
    (cs : List Chal) (format : Fin (n + 1) → Option (Chal × Resp) → T)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    searchesQueryCount σ ρ b M (n + 1) e pk sk sc msg comList cs format cache =
      (do
        let z ← searchCostRun σ ρ b M pk sk (sc 0) msg comList (e 0) cs none cache
        let tail ← searchesQueryCount σ ρ b M n (fun j => e j.succ) pk sk
          (fun j => sc j.succ) msg comList cs (fun j => format j.succ) z.2
        return z.1.2.toAdd + tail) := by
  simp [searchesQueryCount, searchesCostRun, searchCostRun, HasQuery.Program.withUnitCost,
    Fin.mOfFn, WriterT.run_bind, StateT.run_bind, map_bind, monad_norm]

private theorem integral_count_add (c : ℕ) (run : ProbComp ℕ) :
    ∫⁻ (n : ℕ), (n : ℝ≥0∞) ∂𝒟[(fun n : ℕ => c + n) <$> run] =
      c + ∫⁻ (n : ℕ), (n : ℝ≥0∞) ∂𝒟[run] := by
  rw [lintegral_evalDist_map run Measurable.of_discrete Measurable.of_discrete]
  simp only [Nat.cast_add]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- Expected query count for sequential searches at distinct repetition tags. The cache may
contain other records, but every candidate at a selected repetition must initially be fresh. -/
theorem searches_expectedQueries {T : Type} (n : ℕ) (e : Fin n → Fin ρ)
    (he : Function.Injective e) (pk : Stmt) (sk : Wit) (sc : Fin n → PrvState)
    (msg : M) (comList : List Commit) (cs : List Chal) (hcs : cs.Nodup)
    (format : Fin n → Option (Chal × Resp) → T)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hfresh : ∀ j c, c ∈ cs → ∀ r, cache ⟨pk, msg, comList, e j, c, r⟩ = none) :
    ∫⁻ (q : ℕ), (q : ℝ≥0∞)
      ∂𝒟[searchesQueryCount σ ρ b M n e pk sk sc msg comList cs format cache] =
        n * ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
  classical
  let : MeasurableSpace ((Option (Chal × Resp) × Multiplicative ℕ) ×
      (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) := ⊤
  induction n generalizing cache with
  | zero =>
    simp [searchesQueryCount, searchesCostRun, Fin.mOfFn, HasQuery.Program.withUnitCost]
  | succ n ih =>
    have htail (z) (hz : z ∈ support
        (searchCostRun σ ρ b M pk sk (sc 0) msg comList (e 0) cs none cache)) :
        ∫⁻ (q : ℕ), (q : ℝ≥0∞)
          ∂𝒟[searchesQueryCount σ ρ b M n (fun j => e j.succ) pk sk
            (fun j => sc j.succ) msg comList cs (fun j => format j.succ) z.2] =
          n * ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
      apply ih
      · exact he.comp (Fin.succ_injective _)
      · intro j c hc r
        rw [searchCostRun_preserves_offrep σ ρ b M pk sk (sc 0) msg comList (e 0) cs
          hcs none cache (fun c hc r => hfresh 0 c hc r) hz
          ⟨pk, msg, comList, e j.succ, c, r⟩
          (fun h => Fin.succ_ne_zero j (he h))]
        exact hfresh j.succ c hc r
    rw [searchesQueryCount_succ]
    simp only [bind_pure_comp]
    rw [lintegral_evalDist_bind _ _ Measurable.of_discrete Measurable.of_discrete]
    have hae := OracleComp.ae_of_forall_mem_support
      (searchCostRun σ ρ b M pk sk (sc 0) msg comList (e 0) cs none cache) _ htail
    calc
      _ = ∫⁻ z, (z.1.2.toAdd : ℝ≥0∞) +
          n * ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j
          ∂𝒟[searchCostRun σ ρ b M pk sk (sc 0) msg comList (e 0) cs none cache] := by
        apply lintegral_congr_ae
        filter_upwards [hae] with z hz
        rw [integral_count_add, hz]
      _ = searchExpectedQueries σ ρ b M pk sk (sc 0) msg comList (e 0) cs none cache +
          n * ∑ j ∈ Finset.range cs.length, (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
        rw [lintegral_add_left Measurable.of_discrete]
        simp only [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]
        congr 1
        rw [searchExpectedQueries, searchQueryCount,
          lintegral_evalDist_map _ Measurable.of_discrete Measurable.of_discrete]
      _ = _ := by
        rw [searchExpectedQueries_eq_sum σ ρ b M pk sk (sc 0) msg comList (e 0) cs hcs
          none cache (fun c hc r => hfresh 0 c hc r)]
        simp [Nat.cast_add, add_mul, add_comm]

section signing

private theorem run_mOfFn_lift {A State : Type} (n : ℕ) (f : Fin n → ProbComp A)
    (st : State) :
    ((Fin.mOfFn n fun i => (liftM (f i) : AddWriterT ℕ (StateT State ProbComp) A)).run).run st =
      (fun v => ((v, 1), st)) <$> Fin.mOfFn n f := by
  induction n with
  | zero => simp [Fin.mOfFn]
  | succ n ih =>
    have h := ih (fun i => f i.succ)
    simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, monad_norm] at h
    simp [Fin.mOfFn, WriterT.run_bind, StateT.run_bind, liftM, MonadLiftT.monadLift,
      MonadLift.monadLift, h, monad_norm]

variable [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
variable (hr : GenerableRelation Stmt Wit rel) (S : ℕ)

/-- The standard query-cost marginal of the actual Fischlin signer under an empty cached oracle. -/
@[expose]
def signingQueryCount (pk : Stmt) (sk : Wit) (msg : M) : ProbComp ℕ :=
  (HasQuery.queryCountDist
    (fun [HasQuery (fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (AddWriterT ℕ (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp))] =>
      (Fischlin σ hr ρ b S M).sign pk sk msg)
    (randomOracle (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M))).run' ∅

private theorem signingQueryCount_eq (pk : Stmt) (sk : Wit) (msg : M) :
    signingQueryCount σ ρ b M hr S pk sk msg = (do
      let commits ← Fin.mOfFn ρ fun _ => σ.commit pk sk
      searchesQueryCount σ ρ b M ρ id pk sk (fun i => (commits i).2) msg
        (List.ofFn fun i => (commits i).1) (FinEnum.toList Chal)
        (fun i result => match result with
          | some (c, r) => ((commits i).1, c, r)
          | none => ((commits i).1, default, default)) ∅) := by
  simp only [signingQueryCount, HasQuery.queryCountDist, HasQuery.queryCostDist, AddWriterT.costs,
    HasQuery.Program.withAddCost, Fischlin, QueryImpl.toHasQuery_query, QueryImpl.withAddCost_apply,
    QueryImpl.withCaching_apply, uniformSampleImpl_apply, bind_pure_comp,
    map_eq_bind_pure_comp, WriterT.run_bind, Function.comp_apply,
    toAdd_mul, StateT.run'_eq, StateT.run_bind, run_mOfFn_lift,
    StateT.run_pure, bind_assoc, pure_bind, toAdd_one, zero_add,
    searchesQueryCount, searchesCostRun, HasQuery.Program.withUnitCost, id_eq]
  apply bind_congr
  intro commits
  apply congrArg (fun run : AddWriterT ℕ
    (StateT (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache ProbComp)
      (Fin ρ → Commit × Chal × Resp) =>
    run.run.run ∅ >>= pure ∘ fun z => z.1.2.toAdd)
  apply congrArg (Fin.mOfFn ρ)
  funext i
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some pair => cases pair; rfl

/-- The actual honest signer's expected hash calls equal the sum of its truncated geometric
search costs. Repetition indices and distinct enumerated challenges discharge freshness. -/
theorem sign_expectedQueries_eq_sum (pk : Stmt) (sk : Wit) (msg : M) :
    ∫⁻ (q : ℕ), (q : ℝ≥0∞) ∂𝒟[signingQueryCount σ ρ b M hr S pk sk msg] =
      ρ * ∑ j ∈ Finset.range (FinEnum.card Chal), (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
  let : MeasurableSpace (Fin ρ → Commit × PrvState) := ⊤
  rw [signingQueryCount_eq,
    lintegral_evalDist_bind _ _ Measurable.of_discrete Measurable.of_discrete]
  have hsearch (commits : Fin ρ → Commit × PrvState) :
      ∫⁻ (q : ℕ), (q : ℝ≥0∞)
        ∂𝒟[searchesQueryCount σ ρ b M ρ id pk sk (fun i => (commits i).2) msg
          (List.ofFn fun i => (commits i).1) (FinEnum.toList Chal)
          (fun i result => match result with
            | some (c, r) => ((commits i).1, c, r)
            | none => ((commits i).1, default, default)) ∅] =
        ρ * ∑ j ∈ Finset.range (FinEnum.card Chal), (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ j := by
    simpa [FinEnum.toList] using searches_expectedQueries σ ρ b M ρ id Function.injective_id pk sk
      (fun i => (commits i).2) msg (List.ofFn fun i => (commits i).1)
      (FinEnum.toList Chal) FinEnum.nodup_toList
      (fun i result => match result with
        | some (c, r) => ((commits i).1, c, r)
        | none => ((commits i).1, default, default)) ∅ (by simp)
  simp_rw [hsearch]
  simp only [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- Closed geometric form of the actual signer's expected number of hash calls. -/
theorem sign_expectedQueries_eq_geometric (pk : Stmt) (sk : Wit) (msg : M) :
    ∫⁻ (q : ℕ), (q : ℝ≥0∞) ∂𝒟[signingQueryCount σ ρ b M hr S pk sk msg] =
      ρ * (2 ^ b : ℝ≥0∞) *
        (1 - (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ FinEnum.card Chal) := by
  rw [sign_expectedQueries_eq_sum, geometricSearchSum_eq]
  exact (mul_assoc _ _ _).symm

end signing

end Fischlin

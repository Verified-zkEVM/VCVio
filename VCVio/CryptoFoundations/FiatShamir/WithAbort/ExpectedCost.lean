/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Cost
public import VCVio.EvalDist.Monad.Branch
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Expected-cost theorems for Fiat-Shamir with aborts

Expected random-oracle query costs of `fsAbortSignLoop` and
`FiatShamirWithAbort.sign`/`verify`, stated as tail-probability identities over the
induced output measures. These drive the aggregate runtime bounds used in the security proof.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section expectedCost

variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) (M : Type)

variable {m : Type → Type u} [Monad m] [MonadLiftT ProbComp m]

private lemma signLoop_inRuntime_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.Program.eval
              (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg n)
              runtime) :=
  rfl

section

variable [LawfulMonad m]

private lemma signLoop_queryCountDist_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.queryCountDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some _ => pure 1
        | none =>
            let recCosts :=
              HasQuery.queryCountDist
                (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
                runtime
            Nat.succ <$> recCosts) := by
  rw [HasQuery.queryCountDist, HasQuery.queryCostDist]
  simp only [fsAbortSignLoop, HasQuery.Program.withAddCost_bind]
  rw [AddWriterT.costs_def, WriterT.run_bind, signAttempt_run_withUnitCost_eq]
  simp only [bind_map_left, map_bind, Functor.map_map, toAdd_mul, toAdd_ofAdd]
  refine bind_congr ?_
  intro attempt
  cases attempt.2 with
  | some z =>
      simp
  | none =>
      simp [HasQuery.queryCountDist, HasQuery.queryCostDist,
        HasQuery.Program.withAddCost, AddWriterT.costs, add_comm]

private lemma signLoop_queryCountDist_succ_ite
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.queryCountDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1)) runtime =
      (HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
          fsAbortSignAttempt (m := m) ids M pk sk msg) runtime >>= fun attempt ↦
        if attempt.2 = none then
          Nat.succ <$> HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n) runtime
        else pure 1) := by
  classical
  rw [signLoop_queryCountDist_succ]
  apply bind_congr
  intro attempt
  cases attempt.2 <;> simp

end

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The propositional observation of whether one signing attempt aborts. Its successful mass
records whether the underlying attempt completed, separately from the abort outcome. -/
abbrev signAttemptAborts
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) : m Prop :=
  (fun attempt ↦ attempt.2 = none) <$> HasQuery.Program.eval
    (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
      fsAbortSignAttempt (m := m) ids M pk sk msg) runtime

/-- The probability that a single Fiat-Shamir-with-aborts signing attempt aborts. -/
noncomputable abbrev signAttemptAbortProbability
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) : ENNReal :=
  𝒟[signAttemptAborts ids M runtime pk sk msg] {True}

variable [LawfulMonad m]

omit [LawfulEvalDistSemantics m] in
/-- Single-attempt abort probability is the final event that the attempt returns no response. -/
@[simp]
lemma signAttemptAbortProbability_eq_prEvent
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    signAttemptAbortProbability ids M runtime pk sk msg = Pr{
      let attempt ← HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
          fsAbortSignAttempt (m := m) ids M pk sk msg) runtime}[attempt.2 = none] :=
  (prEvent_eq_evalDist_map _ _).symm

private lemma signLoop_probNone_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    Pr{
      let sig ← HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
          fsAbortSignLoop (m := m) ids M pk sk msg (n + 1)) runtime}[sig = none] =
      signAttemptAbortProbability ids M runtime pk sk msg *
        Pr{
          let sig ← HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
              fsAbortSignLoop (m := m) ids M pk sk msg n) runtime}[sig = none] := by
  classical
  rw [signLoop_inRuntime_succ, signAttemptAbortProbability_eq_prEvent]
  apply prEvent_bind_eq_mul_of_ite
  intro attempt
  cases attempt.2 <;> simp

private lemma signLoop_queryTailProbability_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (i n : ℕ) :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1)) runtime}[i + 1 < q] =
      signAttemptAbortProbability ids M runtime pk sk msg *
        Pr{
          let q ← HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n) runtime}[i < q] := by
  classical
  rw [signLoop_queryCountDist_succ, signAttemptAbortProbability_eq_prEvent]
  apply prEvent_bind_eq_mul_of_ite
  intro attempt
  cases attempt.2 <;> simp

/-- A lossless abort observation makes the bounded signing loop's query-count measure lossless.
Only the finite observation is measured; commitments and responses need no measurable spaces. -/
instance isProbabilityMeasure_signLoop_queryCountDist
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]] (n : ℕ) :
    MeasureTheory.IsProbabilityMeasure 𝒟[HasQuery.queryCountDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n) runtime] := by
  classical
  induction n with
  | zero =>
      simpa [HasQuery.queryCountDist, HasQuery.Program.withAddCost, fsAbortSignLoop] using
        (inferInstance : MeasureTheory.IsProbabilityMeasure 𝒟[(pure 0 : m ℕ)])
  | succ n ih =>
      let := ih
      let := evalDist.isProbabilityMeasure_map (f := Nat.succ)
        (HasQuery.queryCountDist
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n) runtime)
        Measurable.of_discrete
      rw [signLoop_queryCountDist_succ_ite]
      apply evalDist.isProbabilityMeasure_bind_ite

private lemma signLoop_queryTailProbability_zero
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]] :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1)) runtime}[0 < q] = 1 := by
  rw [prEvent_eq_evalDist_of_discrete]
  have hzero : 𝒟[HasQuery.queryCountDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1)) runtime] {0} = 0 := by
    rw [← prEvent_eq_evalDist_singleton, signLoop_queryCountDist_succ_ite,
      prEvent_bind_ite]
    simp only [prEvent_map, Nat.succ_ne_zero, prEvent_false, mul_zero, zero_add]
    simp
  have hset : {q : ℕ | 0 < q} = ({0} : Set ℕ)ᶜ := by ext q; simp [Nat.pos_iff_ne_zero]
  rw [hset, MeasureTheory.measure_compl (measurableSet_singleton 0)
    (by rw [hzero]; exact ENNReal.zero_ne_top), hzero, MeasureTheory.measure_univ]
  exact tsub_zero 1

private theorem signLoop_queryTailProbability_eq_probNonePrefix
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]]
    (i extra : ℕ) :
      Pr{
        let q ← HasQuery.queryCountDist
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] ↦
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1)) runtime}[i < q] =
        Pr{
          let sig ← HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
              fsAbortSignLoop (m := m) ids M pk sk msg i) runtime}[sig = none] := by
  induction i with
  | zero =>
      rw [Nat.zero_add, signLoop_queryTailProbability_zero ids M runtime pk sk msg extra]
      simp [HasQuery.Program.eval, fsAbortSignLoop]
  | succ i ih =>
      rw [Nat.add_right_comm i 1 extra,
        signLoop_queryTailProbability_succ (i := i) (n := i + extra + 1), ih,
        ← signLoop_probNone_succ (n := i)]

/-- The first `i` attempts all abort with the `i`-th power of the one-attempt abort probability.
Missing mass is not an abort outcome. -/
theorem sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ i,
      Pr{
        let sig ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] ↦
            fsAbortSignLoop (m := m) ids M pk sk msg i) runtime}[sig = none] =
        signAttemptAbortProbability ids M runtime pk sk msg ^ i
  | 0 => by
      simp [signAttemptAbortProbability, HasQuery.Program.eval, fsAbortSignLoop]
  | i + 1 => by
      rw [signLoop_probNone_succ,
        sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
          (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i,
        pow_succ']

section schemeCost

variable (hr : GenerableRelation Stmt Wit rel)

/-- The probability that signing makes more than `i` random-oracle queries is exactly the
probability that the first `i` signing attempts all abort.

Equivalently, the event `i < q` for the signer query count is the event that the retry loop of
length `i` returns `none`, meaning that the `(i + 1)`-st attempt is reached. -/
theorem sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]]
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime}[i < q] =
      Pr{
        let sig ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime}[sig = none] := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt hi
  exact signLoop_queryTailProbability_eq_probNonePrefix
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (i := i) (extra := extra)

/-- The probability that signing makes more than `i` oracle queries is the `i`-th power of the
single-attempt abort probability, as long as `i < maxAttempts`. -/
theorem sign_queryTailProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]]
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime}[i < q] =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  rw [sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (hr := hr) (hi := hi)]
  exact sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
    (ids := ids) (M := M) runtime pk sk msg i

/-- Once `i` reaches `maxAttempts`, the signer never makes more than `i` queries, so the tail
event has probability zero. -/
private theorem sign_queryTailProbability_eq_zero_of_le
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    {i maxAttempts : ℕ} (hi : maxAttempts ≤ i) :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime}[i < q] = 0 := by
  induction maxAttempts generalizing i with
  | zero =>
      simp [FiatShamirWithAbort, HasQuery.queryCountDist, HasQuery.Program.withAddCost,
        fsAbortSignLoop]
  | succ n ih =>
      cases i with
      | zero => omega
      | succ i =>
          simp only [FiatShamirWithAbort] at ih ⊢
          rw [signLoop_queryTailProbability_succ, ih (by omega), mul_zero]

/-- The expected number of signing queries is the sum, over prefixes of the retry loop, of the
probability that every attempt in the prefix aborts. -/
theorem sign_expectedQueries_eq_sum_abortPrefixProbabilities
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]]
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr{
          let sig ← HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime}[sig = none] := by
  rw [HasQuery.expectedQueries_eq_tsum_tail_probs]
  rw [tsum_eq_sum (s := Finset.range maxAttempts) (fun i hi ↦
    sign_queryTailProbability_eq_zero_of_le ids M hr runtime pk sk msg
      (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hi)))]
  exact Finset.sum_congr rfl fun i hi =>
    sign_queryTailProbability_eq_probAllFirstAttemptsAbort
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (hi := Finset.mem_range.mp hi)

/-- The expected number of signing queries is the finite geometric sum of the one-step abort
probability. -/
theorem sign_expectedQueries_eq_sum_signAttemptAbortProbability_powers
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    [MeasureTheory.IsProbabilityMeasure 𝒟[signAttemptAborts ids M runtime pk sk msg]]
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  rw [sign_expectedQueries_eq_sum_abortPrefixProbabilities (ids := ids) (hr := hr) (M := M)
    (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (maxAttempts := maxAttempts)]
  exact Finset.sum_congr rfl fun i _ =>
    sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow ids M runtime pk sk msg i

/-- Tail probabilities for the signer query count are bounded by the corresponding power of the
single-attempt abort probability. -/
theorem sign_queryTailProbability_le_signAttemptAbortProbability_pow
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (i maxAttempts : ℕ) :
    Pr{
      let q ← HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime}[i < q] ≤
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  induction i generalizing maxAttempts with
  | zero =>
      rw [pow_zero]
      apply MeasureTheory.measure_le_one
  | succ i ih =>
      cases maxAttempts with
      | zero =>
          simp [FiatShamirWithAbort, HasQuery.queryCountDist, HasQuery.Program.withAddCost,
            fsAbortSignLoop]
      | succ n =>
          simp only [FiatShamirWithAbort] at ih ⊢
          rw [signLoop_queryTailProbability_succ, pow_succ']
          exact mul_le_mul_right (ih n) _

/-- The expected number of signing queries is bounded by the infinite geometric series generated by
the single-attempt abort probability. -/
theorem sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  HasQuery.expectedQueries_le_tsum_of_tail_probs_le _ runtime fun i ↦
    sign_queryTailProbability_le_signAttemptAbortProbability_pow
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (i := i) (maxAttempts := maxAttempts)

/-- If the single-attempt abort probability is bounded by `q`, then the expected number of signing
queries is bounded by the corresponding geometric series. -/
theorem sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) {q : ENNReal}
    (hq : signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg ≤ q) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      (1 - q)⁻¹ := by
  calc
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
      sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers ids M hr runtime pk sk msg
        maxAttempts
    _ ≤ ∑' i : ℕ, q ^ i := by gcongr
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- Specializing the geometric upper bound to the actual one-step abort probability yields the
canonical infinite geometric upper bound on expected query count. -/
theorem sign_expectedQueries_le_geometric
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      (1 - signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg)⁻¹ :=
  sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    ids M hr runtime pk sk msg maxAttempts le_rfl

/-- Verification's expected weighted query cost is the queried commitment's valuation when a
signature is present, and the valuation of zero otherwise. -/
theorem verify_expectedQueryCost_eq
    {ω : Type} [MeasurableSpace ω] [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Option (Commit × Resp))
    (costFn : M × Commit → ω) (val : ω → ENNReal) (hval : Measurable val) (maxAttempts : ℕ)
    [MeasureTheory.IsProbabilityMeasure 𝒟[HasQuery.queryCostDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] ↦
        (FiatShamirWithAbort ids hr M maxAttempts).verify pk msg sig) runtime costFn]] :
    ExpectedQueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).verify pk msg sig in runtime by costFn via val
    ] = match sig with
      | none => val 0
      | some (w', _) => val (costFn (msg, w')) := by
  cases sig with
  | none =>
      simpa only [HasQuery.expectedQueryCost, HasQuery.Program.withAddCost,
        FiatShamirWithAbort] using (AddWriterT.expectedCost_pure false val hval)
  | some sig =>
      apply HasQuery.expectedQueryCost_eq_of_usesCostExactly (hval := hval)
      simp [HasQuery.UsesCostExactly, AddWriterT.hasCost_iff, FiatShamirWithAbort,
        HasQuery.Program.withAddCost, QueryImpl.withAddCost_apply, AddWriterT.outputs,
        AddWriterT.costs, AddWriterT.addTell]

end schemeCost

end expectedCost

end FiatShamirWithAbort

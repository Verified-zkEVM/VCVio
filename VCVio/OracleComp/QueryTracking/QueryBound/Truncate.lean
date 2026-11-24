/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Batch
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Truncating a program at a round bound

`truncate r k₀ oa` runs a round-structured program `oa : OracleComp (free + spec.batch) α` until
it would submit round `r + 1`, and returns the fallback `k₀` there instead. Its queries to the
summand `free`, which cost no round, are kept, and so is its output after the last permitted
round. The truncation is defined on the free monad itself, so it never answers a query it cuts
off.

The rounds a run completes are counted by instrumenting the handler: `runCountingRounds impl oa`
is the run of `oa` under `impl` with an additive writer counting one per round
(`QueryImpl.withAddCost`), and its first component is the plain run `simulateQ impl oa`
(`fst_map_runCountingRounds`). A run *outputs `x` within `r` rounds* when it returns `(x, n)` with
`n ≤ r`.

## Main statements

* `IsPointQueryBound.isOnlineQueryBound_truncate`: the truncation of a program with point budget
  `q` has online budget `(r, q)`.
* `IsPointQueryBound.truncate`: truncation preserves the point budget.
* `truncate_eq_self_of_isOnlineQueryBound`: a program already within `r` rounds is unchanged.
* `prEvent_runCountingRounds_le_truncate`: under any handler, the probability that `oa` outputs a
  value satisfying `p` within `r` completed rounds is at most the probability that its truncation
  outputs a value satisfying `p`.
* `prEvent_run_runCountingRounds_le_truncate`: the same for a stateful handler run from any
  state, with the event also reading the final state.
* `simulateQ_runCountingRounds`, `simulateQ_runCountingRounds_unbatch`: counting the rounds and
  then simulating the handler's answers, or unbatching, is counting the rounds under the composed
  or batched handler.
* `prEvent_run_runCountingRounds_le_of_isOnlineQueryBound`: under any stateful handler, a program
  within `r` rounds completes at most `r` rounds.
-/

public section

open OracleSpec

namespace OracleComp

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-! ## The truncation -/

/-- Run `oa` until it would submit round `r + 1`, and return `k₀` there instead. Queries to the
free summand pass through, and every output reached within `r` rounds is kept. -/
def truncate : ℕ → α → OracleComp (free + spec.batch) α →
    OracleComp (free + spec.batch) α
  | _, _, .pure x => pure x
  | r, k₀, .queryBind (Sum.inl n) k => .queryBind (Sum.inl n) fun u => truncate r k₀ (k u)
  | 0, k₀, .queryBind (Sum.inr _) _ => pure k₀
  | r + 1, k₀, .queryBind (Sum.inr ts) k => .queryBind (Sum.inr ts) fun u => truncate r k₀ (k u)

variable (r : ℕ) (k₀ : α)

@[simp] lemma truncate_pure (x : α) :
    truncate (free := free) (spec := spec) r k₀ (pure x) = pure x := by
  rfl

@[simp] lemma truncate_query_bind_inl (n : τ)
    (k : (free + spec.batch).Range (.inl n) → OracleComp (free + spec.batch) α) :
    truncate r k₀ (liftM ((free + spec.batch).query (.inl n)) >>= k) =
      liftM ((free + spec.batch).query (.inl n)) >>= fun u => truncate r k₀ (k u) := by
  rfl

@[simp] lemma truncate_zero_query_bind_inr (ts : List ι)
    (k : (free + spec.batch).Range (.inr ts) → OracleComp (free + spec.batch) α) :
    truncate 0 k₀ (liftM ((free + spec.batch).query (.inr ts)) >>= k) = pure k₀ := by
  rfl

@[simp] lemma truncate_succ_query_bind_inr (ts : List ι)
    (k : (free + spec.batch).Range (.inr ts) → OracleComp (free + spec.batch) α) :
    truncate (r + 1) k₀ (liftM ((free + spec.batch).query (.inr ts)) >>= k) =
      liftM ((free + spec.batch).query (.inr ts)) >>= fun u => truncate r k₀ (k u) := by
  rfl

variable {r k₀}

/-! ## Budgets of the truncation -/

/-- The truncation at `r` rounds of a program with point budget `q` has online budget `(r, q)`. -/
theorem IsPointQueryBound.isOnlineQueryBound_truncate {oa : OracleComp (free + spec.batch) α}
    {q : ℕ} (h : IsPointQueryBound oa q) : IsOnlineQueryBound (truncate r k₀ oa) (r, q) := by
  induction oa using OracleComp.inductionOn generalizing r q with
  | pure x => trivial
  | query_bind t k ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rcases t with n | ts
      · rw [truncate_query_bind_inl, isOnlineQueryBound_query_bind_inl_iff]
        exact fun u => ih u (by simpa using hk u)
      · cases r with
        | zero => trivial
        | succ r =>
            rw [truncate_succ_query_bind_inr, isOnlineQueryBound_query_bind_inr_iff]
            exact ⟨⟨r.succ_pos, by simpa using ht⟩, fun u => ih u (hk u)⟩

/-- Truncation preserves the point budget. -/
theorem IsPointQueryBound.truncate {oa : OracleComp (free + spec.batch) α} {q : ℕ}
    (h : IsPointQueryBound oa q) : IsPointQueryBound (OracleComp.truncate r k₀ oa) q :=
  (h.isOnlineQueryBound_truncate (r := r) (k₀ := k₀)).isPointQueryBound

/-- A program within `r` rounds is its own truncation at `r` rounds. -/
theorem truncate_eq_self_of_isOnlineQueryBound {oa : OracleComp (free + spec.batch) α}
    {q : ℕ} (h : IsOnlineQueryBound oa (r, q)) : truncate r k₀ oa = oa := by
  induction oa using OracleComp.inductionOn generalizing r q with
  | pure x => rfl
  | query_bind t k ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rcases t with n | ts
      · rw [truncate_query_bind_inl]
        exact bind_congr fun u => ih u (hk u)
      · obtain ⟨hr, -⟩ := ht
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
        rw [truncate_succ_query_bind_inr]
        exact bind_congr fun u => ih u (by simpa using hk u)

/-! ## Outputs within a round bound -/

/-- The rounds a single query submits: none for a query to the free summand, and one for a
round. -/
@[expose]
def roundCount : τ ⊕ List ι → ℕ
  | .inl _ => 0
  | .inr _ => 1

@[simp] lemma roundCount_inl (n : τ) : roundCount (ι := ι) (.inl n) = 0 := rfl

@[simp] lemma roundCount_inr (ts : List ι) : roundCount (τ := τ) (.inr ts) = 1 := rfl

variable {m : Type → Type*} [Monad m]

/-- Run `oa` under `impl`, returning its output together with the number of rounds the run
completed. The first component is the run `simulateQ impl oa` itself
(`fst_map_runCountingRounds`). -/
abbrev runCountingRounds (impl : QueryImpl (free + spec.batch) m)
    (oa : OracleComp (free + spec.batch) α) : m (α × ℕ) :=
  (simulateQ (impl.withAddCost roundCount) oa).runAdd

variable [LawfulMonad m] (impl : QueryImpl (free + spec.batch) m)

lemma fst_map_runCountingRounds (oa : OracleComp (free + spec.batch) α) :
    Prod.fst <$> runCountingRounds impl oa = simulateQ impl oa := by
  rw [AddWriterT.fst_map_runAdd]
  exact QueryImpl.fst_map_run_withCost impl _ oa

@[simp] lemma runCountingRounds_pure (x : α) :
    runCountingRounds (free := free) (spec := spec) impl (pure x) = pure (x, 0) := by
  simp [runCountingRounds]

lemma runCountingRounds_query_bind (t : τ ⊕ List ι)
    (k : (free + spec.batch).Range t → OracleComp (free + spec.batch) α) :
    runCountingRounds impl (liftM ((free + spec.batch).query t) >>= k) =
      impl t >>= fun u =>
        (fun z => (z.1, roundCount t + z.2)) <$> runCountingRounds impl (k u) := by
  simp [runCountingRounds, Prod.map]

/-- Under any handler, the probability that `oa` outputs a value satisfying `p` within `r`
completed rounds is at most the probability that its truncation at `r` rounds outputs a value
satisfying `p`. The event is read off the run of `oa` itself, counted by `runCountingRounds`. -/
theorem prEvent_runCountingRounds_le_truncate [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (oa : OracleComp (free + spec.batch) α) (p : α → Prop) :
    Pr{let z ← runCountingRounds impl oa}[z.2 ≤ r ∧ p z.1] ≤
      Pr{let x ← simulateQ impl (truncate r k₀ oa)}[p x] := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure x => simp
  | query_bind t k ih =>
      rw [runCountingRounds_query_bind]
      rcases t with n | ts
      · rw [truncate_query_bind_inl, simulateQ_bind, simulateQ_spec_query]
        refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
        simpa using ih u
      · cases r with
        | zero =>
            refine le_trans (prEvent_bind_le_of_forall_le _ _ _ fun u => ?_) zero_le
            simp
        | succ r =>
            rw [truncate_succ_query_bind_inr, simulateQ_bind, simulateQ_spec_query]
            refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
            simpa [add_comm 1] using ih u

/-- Under any stateful handler run from any state `s`, the probability that `oa` outputs a value
within `r` completed rounds and ends in a state satisfying `p` with it is at most the probability
that its truncation at `r` rounds does. -/
theorem prEvent_run_runCountingRounds_le_truncate [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {σ : Type} (impl : QueryImpl (free + spec.batch) (StateT σ m))
    (oa : OracleComp (free + spec.batch) α) (p : α → σ → Prop) (s : σ) :
    Pr{let z ← (runCountingRounds impl oa).run s}[z.1.2 ≤ r ∧ p z.1.1 z.2] ≤
      Pr{let z ← (simulateQ impl (truncate r k₀ oa)).run s}[p z.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing r s with
  | pure x => simp
  | query_bind t k ih =>
      rw [runCountingRounds_query_bind, StateT.run_bind]
      rcases t with n | ts
      · rw [truncate_query_bind_inl, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
        simpa using ih u.1 u.2
      · cases r with
        | zero =>
            refine le_trans (prEvent_bind_le_of_forall_le _ _ _ fun u => ?_) zero_le
            simp
        | succ r =>
            rw [truncate_succ_query_bind_inr, simulateQ_bind, simulateQ_spec_query,
              StateT.run_bind]
            refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
            simpa [add_comm 1] using ih u.1 u.2

end OracleComp

/-! ## Round counting through simulation and within a round budget -/

namespace OracleComp

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- Simulating the round-counting run of `oa` under `impl` through `so` is the round-counting run
of `oa` under any handler that answers each query as `so` simulates `impl`'s answer. -/
lemma simulateQ_runCountingRounds {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    {m : Type → Type*} [Monad m] [LawfulMonad m] (so : QueryImpl spec' m)
    (impl : QueryImpl (free + spec.batch) (OracleComp spec'))
    (impl' : QueryImpl (free + spec.batch) m) (h : ∀ t, simulateQ so (impl t) = impl' t)
    (oa : OracleComp (free + spec.batch) α) :
    simulateQ so (runCountingRounds impl oa) = runCountingRounds impl' oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [runCountingRounds_query_bind, runCountingRounds_query_bind, simulateQ_bind, h]
      exact bind_congr fun u => by rw [simulateQ_map, ih]

/-- Counting the rounds of `oa` before unbatching and then running under `impl` is counting its
rounds under the batched handler `impl.batch'`. -/
lemma simulateQ_runCountingRounds_unbatch {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (free + spec) m) (oa : OracleComp (free + spec.batch) α) :
    simulateQ impl (runCountingRounds spec.unbatch oa) = runCountingRounds impl.batch' oa := by
  refine simulateQ_runCountingRounds impl _ _ (fun t => ?_) oa
  simpa using QueryImpl.simulateQ_simulateQ_unbatch impl
    (liftM ((free + spec.batch).query t))

/-- Under any stateful handler run from any state `s`, a program within `r` rounds completes at
most `r` rounds: an event of its round-counting run has the probability of the same event
restricted to runs of at most `r` rounds. -/
theorem prEvent_run_runCountingRounds_le_of_isOnlineQueryBound {m : Type → Type*} [Monad m]
    [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {σ : Type}
    (impl : QueryImpl (free + spec.batch) (StateT σ m))
    {oa : OracleComp (free + spec.batch) α} {r q : ℕ} (h : IsOnlineQueryBound oa (r, q))
    (p : α → σ → Prop) (s : σ) :
    Pr{let z ← (runCountingRounds impl oa).run s}[p z.1.1 z.2] ≤
      Pr{let z ← (runCountingRounds impl oa).run s}[z.1.2 ≤ r ∧ p z.1.1 z.2] := by
  induction oa using OracleComp.inductionOn generalizing r q s with
  | pure x => simp
  | query_bind t k ih =>
      obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
      rw [runCountingRounds_query_bind, StateT.run_bind]
      refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun u => ?_
      rcases t with n | ts
      · simpa using ih u.1 (by simpa using hk u.1) u.2
      · obtain ⟨hr, -⟩ := ht
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
        simpa [add_comm 1] using ih u.1 (by simpa using hk u.1) u.2

end OracleComp

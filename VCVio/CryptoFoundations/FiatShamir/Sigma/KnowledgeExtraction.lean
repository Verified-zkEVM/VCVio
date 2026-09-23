/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Fixed-statement Fiat–Shamir extraction

An ordinary prover receives its statement and context before running against an empty
random oracle. Appending the final verification query makes its accepting output forkable.
The named reduction is the existing replay extractor, including its uniform-witness fallback.
-/

public section

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)
variable [DecidableEq M] [DecidableEq Commit]

/-- An ordinary proof-producing program, with statement and context fixed before execution. -/
abbrev KnowledgeProver :=
  Stmt → M → OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Commit × Resp)

/-- Append the verifier's random-oracle query and retain the same candidate proof. -/
@[expose]
def proverWithFinalQuery (prover : KnowledgeProver (Stmt := Stmt)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) M) (msg : M) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir.inROM σ hr M) where
  main pk := do
    let proof ← prover pk msg
    let _ ← HasQuery.query (spec := M × Commit →ₒ Chal) (msg, proof.1)
    return ((msg, proof), ∅)

/-- Execute the real verifier after the ordinary prover using the same initially empty
cached oracle. Uniform queries remain internal randomness; cache misses request fresh challenges. -/
@[expose]
def knowledgeVerifyRun (prover : KnowledgeProver (Stmt := Stmt)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) M) (pk : Stmt) (msg : M) :
    OracleComp (Fork.wrappedSpec Chal) Bool :=
  ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) do
      let proof ← prover pk msg
      (FiatShamir σ hr M).verify pk msg proof).run' (∅, []))

private theorem cache_mem_log {α : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α)
    (st : Fork.SimState M Commit Chal)
    (hinv : ∀ t v, st.1 t = some v → t ∈ st.2)
    {z : α × Fork.SimState M Commit Chal}
    (hz : z ∈ support
      ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) oa).run st)) :
    ∀ t v, z.2.1 t = some v → t ∈ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing st z with
  | pure a =>
    obtain rfl : z = (a, st) := by simpa using hz
    exact hinv
  | query_bind t k ih =>
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    apply ih us.1 us.2 _ hz
    cases t with
    | inl n =>
      have heq := (Fork.mem_support_unifForward_run_iff
        (M := M) (Commit := Commit) (Chal := Chal) n st us).mp hus
      simpa only [heq] using hinv
    | inr mc =>
      change Chal × Fork.SimState M Commit Chal at us
      rcases st with ⟨cache, log⟩
      change us ∈ support ((Fork.roImpl M Commit Chal mc).run (cache, log)) at hus
      cases hc : cache mc with
      | some v =>
        rw [Fork.roImpl_run_some M mc cache log v hc, mem_support_pure_iff] at hus
        obtain rfl := hus
        exact hinv
      | none =>
        rw [Fork.roImpl_run_none M mc cache log hc, mem_support_bind_iff] at hus
        obtain ⟨v, _, hus⟩ := hus
        obtain rfl : us = (v, cache.cacheQuery mc v, log ++ [mc]) := by simpa using hus
        intro t v' ht
        by_cases heq : t = mc
        · simp [heq]
        · have ht' : cache t = some v' :=
            (QueryCache.cacheQuery_of_ne cache v heq).symm.trans ht
          exact List.mem_append_left _ (hinv t v' ht')

private def finishTrace (pk : Stmt) (msg : M) (proof : Commit × Resp)
    (st : Fork.SimState M Commit Chal) : OracleComp (Fork.wrappedSpec Chal)
      (Fork.Trace (Commit := Commit) (Chal := Chal) (Resp := Resp) M) := do
  let (c, st') ← (Fork.roImpl M Commit Chal (msg, proof.1)).run st
  return {
    forgery := (msg, proof)
    advCache := ∅
    roCache := st'.1
    queryLog := st'.2
    verified := σ.verify pk proof.1 c proof.2 }

private theorem runTrace_proverWithFinalQuery [SampleableType Chal]
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) :
    Fork.runTrace σ hr M (proverWithFinalQuery σ hr M prover msg) pk =
      (do
        let (proof, st) ← ((simulateQ
          (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) (prover pk msg)).run
            (∅, []))
        finishTrace σ M pk msg proof st) := by
  simp only [Fork.runTrace, proverWithFinalQuery, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, monad_norm]
  apply bind_congr
  rintro ⟨⟨pc, resp⟩, cache, log⟩
  cases hc : cache (msg, pc) <;>
    simp [finishTrace, HasQuery.query, QueryImpl.simulateQ_add_liftM_query_right,
      Fork.roImpl, hc, monad_norm]

private theorem forkPoint_isSome_eq_verified (Q : ℕ)
    (t : Fork.Trace (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (hmem : t.target ∈ t.queryLog) (hlen : t.queryLog.length ≤ Q + 1) :
    (Fork.forkPoint M Q t).isSome = t.verified := by
  have hidx : t.queryLog.findIdx (· == t.target) < Q + 1 :=
    (List.findIdx_lt_length_of_exists ⟨t.target, hmem, by simp⟩).trans_le hlen
  cases hv : t.verified <;> simp [Fork.forkPoint, hmem, hidx, hv]

private theorem finishTrace_forkable (pk : Stmt) (msg : M) (proof : Commit × Resp)
    (st : Fork.SimState M Commit Chal) (Q : ℕ)
    (hinv : ∀ t v, st.1 t = some v → t ∈ st.2) (hlen : st.2.length ≤ Q)
    {t : Fork.Trace (Commit := Commit) (Chal := Chal) (Resp := Resp) M}
    (ht : t ∈ support (finishTrace σ M pk msg proof st)) :
    (Fork.forkPoint M Q t).isSome = t.verified := by
  rcases st with ⟨cache, log⟩
  cases hc : cache (msg, proof.1) with
  | some c =>
    have heq : t = {
        forgery := (msg, proof)
        advCache := ∅
        roCache := cache
        queryLog := log
        verified := σ.verify pk proof.1 c proof.2 } := by
      simpa [finishTrace, Fork.roImpl, hc] using ht
    subst t
    apply forkPoint_isSome_eq_verified M Q
    · exact hinv _ c hc
    · exact hlen.trans (Nat.le_succ Q)
  | none =>
    simp only [finishTrace, Fork.roImpl, hc, StateT.run_bind, StateT.run_get,
      StateT.run_lift, StateT.run_set, StateT.run_pure, monad_norm,
      mem_support_bind_iff, mem_support_pure_iff] at ht
    obtain ⟨c, _, rfl⟩ := ht
    apply forkPoint_isSome_eq_verified M Q
    · simp [Fork.Trace.target]
    · simpa using Nat.succ_le_succ hlen

/-- The wrapped trace's verifier flag is the verdict of the actual Fiat–Shamir verifier. -/
theorem knowledgeVerifyRun_eq_trace [SampleableType Chal]
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) :
    knowledgeVerifyRun σ hr M prover pk msg =
      (fun t => t.verified) <$>
        Fork.runTrace σ hr M (proverWithFinalQuery σ hr M prover msg) pk := by
  rw [runTrace_proverWithFinalQuery]
  simp [knowledgeVerifyRun, finishTrace, FiatShamir, StateT.run'_eq, StateT.run_bind,
    simulateQ_bind, HasQuery.query, QueryImpl.simulateQ_add_liftM_query_right, monad_norm]

/-- Every supported wrapped trace has a usable fork point exactly when its verifier accepts.
The bound includes the appended verifier slot, including a cache miss at that slot. -/
theorem proverWithFinalQuery_forkable [SampleableType Chal]
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q)
    {t : Fork.Trace (Commit := Commit) (Chal := Chal) (Resp := Resp) M}
    (ht : t ∈ support
      (Fork.runTrace σ hr M (proverWithFinalQuery σ hr M prover msg) pk)) :
    (Fork.forkPoint M Q t).isSome = t.verified := by
  rw [runTrace_proverWithFinalQuery, mem_support_bind_iff] at ht
  obtain ⟨⟨proof, st⟩, hst, ht⟩ := ht
  apply finishTrace_forkable σ M pk msg proof st Q _ _ ht
  · exact cache_mem_log M (prover pk msg) (∅, []) (by simp) hst
  · simpa using Fork.queryLog_length_le_of_nmaHashQueryBound
      (M := M) hQ (∅, []) hst

section probability

variable [SampleableType Chal]

/-- Replay's finite response spaces carry their discrete measurable structure. -/
local instance : ∀ t, MeasurableSpace ((Fork.wrappedSpec Chal).Range t) := fun _ => ⊤

local instance : ∀ t, DiscreteMeasurableSpace ((Fork.wrappedSpec Chal).Range t) :=
  fun _ => inferInstance

/-- The singleton replay challenge oracle uses uniform challenges. -/
noncomputable local instance : IsUniformMeasureSpec (Fork.wrappedSpec Chal) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

/-- Forkable acceptance equals acceptance of the actual verifier for a bounded ordinary prover. -/
theorem forkable_acceptance_eq_verification
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    Pr{
      let t ← Fork.runTrace σ hr M (proverWithFinalQuery σ hr M prover msg) pk
    }[(Fork.forkPoint M Q t).isSome] =
      Pr{let accepted ← knowledgeVerifyRun σ hr M prover pk msg}[accepted = true] := by
  rw [knowledgeVerifyRun_eq_trace]
  simp only [bind_map_left]
  apply congrArg (fun μ : MeasureTheory.Measure Prop => μ {True})
  apply evalDist_bind_congr_of_support
  intro t ht
  rw [proverWithFinalQuery_forkable σ hr M prover pk msg Q hQ ht]

/-- The concrete witness finder: execute the existing replay reduction on the ordinary prover
with its appended verifier query. Its failed-fork branch samples a uniform witness. -/
@[expose]
def knowledgeExtractor [DecidableEq Chal] [SampleableType Wit]
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (msg : M) (Q : ℕ) : Stmt → ProbComp Wit :=
  nmaReduction σ hr M (proverWithFinalQuery σ hr M prover msg) Q

/-- Acceptance of the actual verifier under the chosen native uniform replay-oracle semantics. -/
@[expose]
noncomputable def knowledgeAcceptance
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) : ENNReal :=
  Pr{let accepted ← knowledgeVerifyRun σ hr M prover pk msg}[accepted = true]

/-- An ordinary prover's actual acceptance yields the replay extractor's valid-witness bound.
All subtraction is truncated in `ENNReal`; small challenge spaces can make this bound vacuous. -/
theorem knowledgeExtractor_success [Fintype Chal] [Inhabited Chal] [DecidableEq Chal]
    [SampleableType Wit]
    (hss : σ.SpeciallySound)
    (prover : KnowledgeProver (Stmt := Stmt) (Commit := Commit) (Chal := Chal) (Resp := Resp) M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    let acc := knowledgeAcceptance σ hr M prover pk msg
    acc * (acc / (Q + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr{let w ← knowledgeExtractor σ hr M prover msg Q pk}[rel pk w = true] := by
  have h := pointwise_extraction_bound σ hr M
    (proverWithFinalQuery σ hr M prover msg) Q hss pk
  dsimp only [knowledgeAcceptance] at h ⊢
  rwa [forkable_acceptance_eq_verification σ hr M prover pk msg Q hQ] at h

end probability

end FiatShamir

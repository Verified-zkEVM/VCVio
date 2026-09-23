/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction
public import VCVio.CryptoFoundations.ReplayForkCost
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Fiat–Shamir replay extraction costs

A prover bounded by `Q` source hash calls gives an actual replay extractor bounded by
`2 * (Q + 1)` fresh challenge requests. The final verifier slot is included. Cache hits
and pure cursor traversal are not fresh challenge requests; internal uniform randomness
is a separate resource. The bound includes all failed-fork branches.
-/

public section

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

private theorem simulated_hash_bound [DecidableEq M] [DecidableEq Commit] {A : Type}
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) A) (Q : ℕ)
    (hQ : nmaHashQueryBound (M := M) (oa := oa) Q) (st : Fork.SimState M Commit Chal) :
    IsQueryBoundP
      ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) oa).run st)
      (· = .inr ()) Q := by
  apply hQ.simulateQ_run_StateT_of_step
  intro t st
  cases t with
  | inl n =>
    change IsQueryBoundP ((Fork.unifForward M Commit Chal n).run st) (· = .inr ()) 0
    simp [Fork.unifForward_run, Fork.wrappedUniformQuery]
  | inr mc =>
    change IsQueryBoundP ((Fork.roImpl M Commit Chal mc).run st) (· = .inr ()) 1
    rcases st with ⟨cache, log⟩
    cases hc : cache mc with
    | none =>
      simp [Fork.roImpl_run_none M mc cache log hc, Fork.wrappedChallengeQuery]
    | some v => simp [Fork.roImpl_run_some M mc cache log v hc]

/-- The final-query adapter costs at most one extra source hash call. -/
theorem proverWithFinalQuery_hash_bound
    (prover : KnowledgeProver Stmt Commit Chal Resp M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    nmaHashQueryBound (M := M)
      (oa := (proverWithFinalQuery σ hr M prover msg).main pk) (Q + 1) := by
  unfold proverWithFinalQuery nmaHashQueryBound
  apply isQueryBoundP_bind hQ
  intro proof _
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  change IsQueryBoundP
    (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (.inr (msg, proof.1)))) _ 1
  simp

variable [DecidableEq M] [DecidableEq Commit]

/-- Cache misses in the actual wrapped verifier trace obey the source query budget. -/
theorem proverWithFinalQuery_trace_bound [SampleableType Chal]
    (prover : KnowledgeProver Stmt Commit Chal Resp M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    IsQueryBoundP (Fork.runTrace σ hr M (proverWithFinalQuery σ hr M prover msg) pk)
      (· = .inr ()) (Q + 1) := by
  unfold Fork.runTrace
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  exact simulated_hash_bound M _ _
    (proverWithFinalQuery_hash_bound σ hr M prover pk msg Q hQ) _

private theorem lifted_randomness_bound {A : Type} (oa : ProbComp A) :
    IsQueryBoundP (liftComp oa (Fork.wrappedSpec Chal)) (· = .inr ()) 0 :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (by intro t; simp [SubSpec.onQuery]) (isQueryBoundP_false oa 0)

/-- The same replay program consumed by `knowledgeExtractor` requests at most `2 * (Q + 1)`
fresh challenges. Extraction and uniform-witness fallback add no challenge requests. -/
theorem knowledgeExtractor_challenge_bound [DecidableEq Chal]
    [SampleableType Chal] [SampleableType Wit]
    (prover : KnowledgeProver Stmt Commit Chal Resp M)
    (pk : Stmt) (msg : M) (Q : ℕ) (hQ : nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    IsQueryBoundP
      (nmaForkExtract σ hr M (proverWithFinalQuery σ hr M prover msg) Q pk)
      (· = .inr ()) (2 * (Q + 1)) := by
  have hf := isQueryBoundP_contextFork (· = .inr ()) _ (nmaForkBudget Q) (.inr ())
    (Fork.forkPoint _ _ _ M Q) (Q + 1) (proverWithFinalQuery_trace_bound σ hr M prover pk msg Q hQ)
  have hb (pair) : IsQueryBoundP (nmaForkExtractBranch (M := M) σ pair) (· = .inr ()) 0 := by
    unfold nmaForkExtractBranch
    repeat' first | exact lifted_randomness_bound _ | split
  simpa [nmaForkExtract, two_mul] using isQueryBoundP_bind hf (fun pair _ => hb pair)

end FiatShamir

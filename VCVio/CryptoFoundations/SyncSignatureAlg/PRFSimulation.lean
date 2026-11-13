/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.ProjectedQueries
public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Cached PRF simulation for synchronized signing

One full-response cache and the actual first-request signing oracle transport adaptive programs.
Per-call output laws and cache freshness invariants preserve complete histories, including failure.
-/

public section
namespace SyncSignatureUnforgeability.PRFSimulation
open OracleComp OracleSpec ProbabilityTheory MeasureTheory
open OracleComp.ProgramLogic.Relational


/-- Per-query couplings preserving a state relation transport the complete adaptive view. -/
private theorem adaptiveRun_projected {ι A S T : Type} {spec : OracleSpec ι}
    (left : QueryImpl spec (StateT S ProbComp))
    (right : QueryImpl spec (StateT T ProbComp)) (project : S → T)
    (relation : S → T → Prop)
    (hproject : ∀ s t, relation s t → project s = t)
    (hstep : ∀ q s t, relation s t → RelTriple ((left q).run s) ((right q).run t)
      (fun a b => a.1 = b.1 ∧ relation a.2 b.2))
    (program : OracleComp spec A) (s : S) (t : T) (hstate : relation s t) :
    Prod.map id project <$> (simulateQ left program).run s =ᵈ
      (simulateQ right program).run t := by
  have hrel := relTriple_simulateQ_run left right relation program hstep s t hstate
  have hmap := evalDistEq_map_of_relTriple
    (f := Prod.map id project) (g := id) (by
      apply relTriple_post_mono hrel
      intro a b hab
      exact Prod.ext hab.1 (hproject a.2 b.2 hab.2))
  simpa only [id_map] using hmap

variable {D Response M PK SK Sig E : Type} [DecidableEq E]

/-- Forward ambient sampling and run the actual first-request signing oracle. -/
@[expose] def signingHandler
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) : QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec E M Sig)
      (StateT (SyncSignatureUnforgeability.History E M Sig)
        (OracleComp (PRFScheme.PRFOracleSpec D Response))) :=
  let forward : QueryImpl unifSpec (OracleComp (PRFScheme.PRFOracleSpec D Response)) :=
    fun q => liftM (OracleSpec.query (Sum.inl q) :
      OracleQuery (PRFScheme.PRFOracleSpec D Response) _)
  forward.liftTarget (StateT (SyncSignatureUnforgeability.History E M Sig)
    (OracleComp (PRFScheme.PRFOracleSpec D Response))) +
    SyncSignatureUnforgeability.signingOracle alg sk

/-- Only a fresh signing request can incur its signer's function-query budget. -/
theorem signingHandler_query_bound
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) (budget : ℕ) (hsign : ∀ ep msg, IsTotalQueryBound (alg.sign sk ep msg) budget)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec E M Sig).Domain)
    (history : SyncSignatureUnforgeability.History E M Sig) :
    IsQueryBoundP ((signingHandler alg sk query).run history)
      (fun q => q.isRight = true) (if query.isRight then budget else 0) := by
  cases query with
  | inl q =>
      simp only [signingHandler, QueryImpl.add_apply_inl]
      unfold QueryImpl.liftTarget
      simp
  | inr request =>
      rcases request with ⟨ep, msg⟩
      change IsQueryBoundP
        (SyncSignatureUnforgeability.signingOracle alg sk (ep, msg) history)
        (fun q => q.isRight = true) budget
      cases hused : history ep with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          trivial
      | none =>
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          change IsQueryBoundP (alg.sign sk ep msg >>= fun answer =>
            pure (answer, Function.update history ep (some (msg, answer))))
            (fun q => q.isRight = true) budget
          simpa only [Nat.add_zero] using isQueryBoundP_bind
            (hsign ep msg).isQueryBoundP (fun answer _ =>
              (show IsQueryBoundP (pure
                (answer, Function.update history ep (some (msg, answer))) :
                  OracleComp (PRFScheme.PRFOracleSpec D Response) _)
                (fun q => q.isRight = true) 0 from trivial))

/-- Run signing and ambient calls with one persistent full-response cache and history. -/
@[expose] def idealHandler [DecidableEq D] [SampleableType Response]
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) : QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec E M Sig)
      (StateT (SyncSignatureUnforgeability.History E M Sig ×
        (D →ₒ Response).QueryCache) ProbComp) :=
  fun query => StateT.mk fun state =>
    (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ => (answer, (nextHistory, nextCache))) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        ((signingHandler alg sk query).run state.1)).run state.2

/-- Run direct signing calls with the same first-request history. -/
@[expose] def fixedHandler (alg : SyncSignatureAlg ProbComp M PK SK Sig E) (sk : SK) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec E M Sig)
      (StateT (SyncSignatureUnforgeability.History E M Sig) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History E M Sig) ProbComp) +
    SyncSignatureUnforgeability.signingOracle alg sk

private theorem idealHandler_uniform
    [DecidableEq D] [SampleableType Response]
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK)
    (q : ℕ) (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (cache : ((D) →ₒ Response).QueryCache) :
    (idealHandler alg sk (Sum.inl q)).run
      (history, cache) =
    (fun response => (response, (history, cache))) <$>
      (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [idealHandler, signingHandler, PRFScheme.prfIdealQueryImpl,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget, unifFwdImpl]


private theorem fixedHandler_uniform
    (alg : SyncSignatureAlg ProbComp M PK SK Sig E) (sk : SK)
    (q : ℕ) (history : SyncSignatureUnforgeability.History (E) M
      (Sig)) :
    (fixedHandler alg sk (Sum.inl q)).run history =
    (fun response => (response, history)) <$>
      (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [fixedHandler, QueryImpl.add_apply_inl, QueryImpl.liftTarget]

/-- A duplicate epoch triggers no oracle call and keeps both cache and history. -/
private theorem idealHandler_used
    [DecidableEq D] [SampleableType Response]
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK)
    (epoch : E) (message : M)
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (cache : ((D) →ₒ Response).QueryCache)
    (first : M) (answer : Option (Sig))
    (hused : history epoch = some (first, answer)) :
    (idealHandler alg sk (Sum.inr (epoch, message))).run
      (history, cache) = pure (none, (history, cache)) := by
  change (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := D) (R := Response))
      (SyncSignatureUnforgeability.signingOracle
        alg sk (epoch, message) history)).run cache = _
  rw [SyncSignatureUnforgeability.signingOracle_used
    alg sk history epoch message first answer hused]
  simp


private theorem fixedHandler_used
    (alg : SyncSignatureAlg ProbComp M PK SK Sig E) (sk : SK)
    (epoch : E) (message : M)
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (first : M) (answer : Option (Sig))
    (hused : history epoch = some (first, answer)) :
    (fixedHandler alg sk (Sum.inr (epoch, message))).run history =
      pure (none, history) := by
  change SyncSignatureUnforgeability.signingOracle
    alg sk (epoch, message) history = _
  exact SyncSignatureUnforgeability.signingOracle_used
    alg sk history epoch message first answer hused

/-- An unused epoch runs one ideal signing computation and records its optional answer. -/
private theorem idealHandler_unused
    [DecidableEq D] [SampleableType Response]
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK)
    (epoch : E) (message : M)
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (cache : ((D) →ₒ Response).QueryCache)
    (hunused : history epoch = none) :
    (idealHandler alg sk (Sum.inr (epoch, message))).run
      (history, cache) =
    (fun result => (result.1,
      (Function.update history epoch (some (message, result.1)), result.2))) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := D) (R := Response))
        (alg.sign sk epoch message)).run cache := by
  change (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := D) (R := Response))
      (SyncSignatureUnforgeability.signingOracle
        alg sk (epoch, message) history)).run cache = _
  rw [SyncSignatureUnforgeability.signingOracle_unused
    alg sk history epoch message hunused]
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]
  simp only [Functor.map_map]
  rfl


private theorem fixedHandler_unused
    (alg : SyncSignatureAlg ProbComp M PK SK Sig E) (sk : SK)
    (epoch : E) (message : M)
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (hunused : history epoch = none) :
    (fixedHandler alg sk (Sum.inr (epoch, message))).run history =
    (fun answer => (answer, Function.update history epoch (some (message, answer)))) <$>
      alg.sign sk epoch message := by
  change SyncSignatureUnforgeability.signingOracle
    alg sk (epoch, message) history = _
  rw [SyncSignatureUnforgeability.signingOracle_unused
    alg sk history epoch message hunused]
  simp [map_eq_bind_pure_comp]
  rfl


private theorem projected_history_update_map
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (epoch : E) (message : M)
    (computation : ProbComp (Option (Sig) ×
      ((D) →ₒ Response).QueryCache)) :
    Prod.map id Prod.fst <$>
      ((fun result => (result.1,
        (Function.update history epoch (some (message, result.1)), result.2))) <$>
        computation) =
    (fun result => (result.1,
      Function.update history epoch (some (message, result.1)))) <$> computation := by
  simp [Functor.map_map, Prod.map]

private theorem mem_support_history_update_map
    (history : SyncSignatureUnforgeability.History (E) M
      (Sig))
    (epoch : E) (message : M)
    (computation : ProbComp (Option (Sig) ×
      ((D) →ₒ Response).QueryCache))
    (result : Option (Sig) ×
      (SyncSignatureUnforgeability.History (E) M
        (Sig) ×
        ((D) →ₒ Response).QueryCache))
    (hresult : result ∈ support
      ((fun signed => (signed.1,
        (Function.update history epoch (some (message, signed.1)), signed.2))) <$>
        computation)) :
    ∃ signed ∈ support computation,
      result = (signed.1,
        (Function.update history epoch (some (message, signed.1)), signed.2)) := by
  rw [support_map] at hresult
  obtain ⟨signed, hsigned, heq⟩ := hresult
  exact ⟨signed, hsigned, heq.symm⟩


/-- Lift one-call signing laws and freshness preservation through the whole adaptive interaction. -/
theorem signingRun_projected {SK' A : Type} [DecidableEq D] [SampleableType Response]
    (oracleAlg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (directAlg : SyncSignatureAlg ProbComp M PK SK' Sig E) (osk : SK) (dsk : SK')
    (fresh : SyncSignatureUnforgeability.History E M Sig → (D →ₒ Response).QueryCache → Prop)
    (hsign : ∀ ep msg history cache, fresh history cache → history ep = none →
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        (oracleAlg.sign osk ep msg)).run' cache =ᵈ directAlg.sign dsk ep msg)
    (hpreserve : ∀ ep msg history cache, fresh history cache → history ep = none →
      ∀ result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        (oracleAlg.sign osk ep msg)).run cache),
      fresh (Function.update history ep (some (msg, result.1))) result.2)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec E M Sig) A)
    (history : SyncSignatureUnforgeability.History E M Sig)
    (cache : (D →ₒ Response).QueryCache) (hfresh : fresh history cache) :
    Prod.map id Prod.fst <$>
      (simulateQ (idealHandler oracleAlg osk) program).run (history, cache) =ᵈ
      (simulateQ (fixedHandler directAlg dsk) program).run history := by
  let relation := fun (left : SyncSignatureUnforgeability.History E M Sig ×
      (D →ₒ Response).QueryCache) (right : SyncSignatureUnforgeability.History E M Sig) =>
    left.1 = right ∧ fresh left.1 left.2
  apply adaptiveRun_projected _ _ Prod.fst relation (fun _ _ h => h.1) _
    program (history, cache) history ⟨rfl, hfresh⟩
  intro query left right hrelated
  rcases left with ⟨hist, table⟩
  rcases hrelated with ⟨rfl, htable⟩
  apply OracleComp.ProgramLogic.Relational.relTriple_of_projected_eq _ _ Prod.fst relation
  · cases query with
    | inl q =>
        rw [idealHandler_uniform, fixedHandler_uniform]
        simp [Functor.map_map]
    | inr request =>
        rcases request with ⟨ep, msg⟩
        cases hused : hist ep with
        | some previous =>
            rcases previous with ⟨first, answer⟩
            rw [idealHandler_used oracleAlg osk ep msg hist table first answer hused,
              fixedHandler_used directAlg dsk ep msg hist first answer hused]
            simp
        | none =>
            rw [idealHandler_unused oracleAlg osk ep msg hist table hused,
              fixedHandler_unused directAlg dsk ep msg hist hused]
            calc
              _ = (fun result => (result.1,
                  Function.update hist ep (some (msg, result.1)))) <$>
                  (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
                    (oracleAlg.sign osk ep msg)).run table :=
                projected_history_update_map hist ep msg _
              _ =ᵈ _ := by
                simpa only [StateT.run'_eq, Functor.map_map] using
                  (hsign ep msg hist table htable hused).map
                    (fun answer => (answer, Function.update hist ep (some (msg, answer))))
  · intro result hresult
    refine ⟨rfl, ?_⟩
    cases query with
    | inl q =>
        rw [idealHandler_uniform] at hresult
        rw [support_map] at hresult
        obtain ⟨answer, _, heq⟩ := hresult
        subst result
        exact htable
    | inr request =>
        rcases request with ⟨ep, msg⟩
        cases hused : hist ep with
        | some previous =>
            rcases previous with ⟨first, answer⟩
            rw [idealHandler_used oracleAlg osk ep msg hist table first answer hused] at hresult
            simp only [support_pure, Set.mem_singleton_iff] at hresult
            subst result
            exact htable
        | none =>
            rw [idealHandler_unused oracleAlg osk ep msg hist table hused] at hresult
            obtain ⟨signed, hsigned, heq⟩ :=
              mem_support_history_update_map hist ep msg _ result hresult
            subst result
            exact hpreserve ep msg hist table htable hused signed hsigned

end SyncSignatureUnforgeability.PRFSimulation

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.Signing
import all HashSig.GXMSS.Security.PRFDerived.KeyMaterial
import all HashSig.GXMSS.Security.PRFDerived.Signing

/-!
# Adaptive cached PRF interaction

The full adaptive signing interaction retains one public parameter and signing core.
Its cached ideal execution has the same returned-output measure as generic GXMSS.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The reduction retains the full signing core after its one key-generation
query sequence. The actual PRF-derived scheme retains only its evaluator key. -/
@[expose] def oracleScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) :
    SyncSignatureAlg
      (OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response))
      M (PublicKey PP H) (GXMSS.SecretKey PP H h v)
        (Signature R H h v) (Fin (2 ^ h)) where
  keygen := do
    let pp ← publicSeedQuery projection
    let starts ← startQueries projection pp
    pure (GXMSS.keys hash pp starts)
  sign := oracleSign hash enc projection budget
  verify := GXMSS.verify hash enc

/-- The source adversary's uniform oracle is forwarded and its signing oracle
uses the shared function interface. A duplicate epoch invokes neither function queries
nor signing and leaves the first-request history unchanged. -/
@[expose] def adaptiveHandler [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v))
        (OracleComp (PRFScheme.PRFOracleSpec
          (GXMSS.PRFDerived.Query PP M h v) Response))) :=
  let alg := oracleScheme hash enc projection budget
  let forward : QueryImpl unifSpec
      (OracleComp (PRFScheme.PRFOracleSpec
        (GXMSS.PRFDerived.Query PP M h v) Response)) :=
    fun q => liftM (OracleSpec.query (Sum.inl q) :
      OracleQuery (PRFScheme.PRFOracleSpec
        (GXMSS.PRFDerived.Query PP M h v) Response) _)
  forward.liftTarget (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v))
        (OracleComp (PRFScheme.PRFOracleSpec
          (GXMSS.PRFDerived.Query PP M h v) Response))) +
      SyncSignatureUnforgeability.signingOracle alg core

/-- Ambient sampling makes no function calls; an eligible signing query makes
exactly its retry budget, including all prefetched draws. -/
private theorem adaptiveHandler_query_bound [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    IsQueryBoundP ((adaptiveHandler hash enc projection budget core query).run history)
      (fun q => q.isRight = true)
      (if query.isRight then budget else 0) := by
  cases query with
  | inl q =>
      change IsQueryBoundP
        ((adaptiveHandler hash enc projection budget core (Sum.inl q)).run history)
        (fun q => q.isRight = true) 0
      simp only [adaptiveHandler, QueryImpl.add_apply_inl]
      -- The source uniform query forwards to the left oracle branch.
      unfold QueryImpl.liftTarget
      simp
  | inr q =>
      rcases q with ⟨epoch, message⟩
      simp only [adaptiveHandler, QueryImpl.add_apply_inr]
      change IsQueryBoundP
        (SyncSignatureUnforgeability.signingOracle
          (oracleScheme hash enc projection budget) core (epoch, message) history)
        (fun q => q.isRight = true) budget
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          trivial
      | none =>
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          change IsQueryBoundP
            (oracleSign hash enc projection budget core epoch message >>= fun answer =>
              pure (answer, Function.update history epoch (some (message, answer))))
            (fun q => q.isRight = true) budget
          have hsum : budget + 0 = budget := by omega
          rw [← hsum]
          apply isQueryBoundP_bind
            (p := fun q => q.isRight = true)
            (oracleSign_bound hash enc projection budget core epoch message).isQueryBoundP
          · intro answer _
            trivial

/-- The ideal function cache and synchronized signing history as one state machine. -/
private def idealAdaptiveHandler [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT ((SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ×
        ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) ProbComp) :=
  fun query => StateT.mk fun state =>
    (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        ((adaptiveHandler hash enc projection budget core query).run state.1)).run state.2

/-- The generic GXMSS signing handler for one fixed key. -/
private def genericFixedHandler [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc budget) sk

/-- Cache states are related to a generic signing state when their consumed-epoch
histories agree and unused epochs have no retry responses. -/
private def CacheRelated
    (pp : PP)
    (left : (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (right : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) : Prop :=
  left.1 = right ∧ RetryFresh (H := H) (R := R) pp left.1 left.2

private theorem relTriple_of_projected_eq
    {A S T : Type} (source : ProbComp (A × S)) (target : ProbComp (A × T))
    (proj : S → T) (relation : S → T → Prop)
    (heq : Prod.map id proj <$> source =ᵈ target)
    (hsource : ∀ result ∈ support source, relation result.2 (proj result.2)) :
    RelTriple source target
      (fun left right => left.1 = right.1 ∧ relation left.2 right.2) := by
  have hself : RelTriple source source
      (fun left right => left.1 = right.1 ∧ relation left.2 (proj right.2)) := by
    apply relTriple_refl_of_mem_support
    intro result hresult
    exact ⟨rfl, hsource result hresult⟩
  have hmap : RelTriple (id <$> source) (Prod.map id proj <$> source)
      (fun left right => left.1 = right.1 ∧ relation left.2 right.2) :=
    relTriple_map (f := id) (g := Prod.map id proj) hself
  simpa only [id_map] using relTriple_of_evalDistEq_right heq hmap

/-- Ambient uniform queries leave the PRF cache unchanged and are forwarded unchanged. -/
private theorem idealAdaptiveHandler_uniform
    [DecidableEq H] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (q : ℕ) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) :
    (idealAdaptiveHandler hash enc projection budget core (Sum.inl q)).run
      (history, cache) =
    (fun response => (response, (history, cache))) <$>
      (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [idealAdaptiveHandler, adaptiveHandler, PRFScheme.prfIdealQueryImpl,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget, unifFwdImpl]

private theorem genericFixedHandler_uniform [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (sk : GXMSS.SecretKey PP H h v)
    (q : ℕ) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    (genericFixedHandler hash enc budget sk (Sum.inl q)).run history =
    (fun response => (response, history)) <$>
      (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [genericFixedHandler, QueryImpl.add_apply_inl, QueryImpl.liftTarget]

/-- A duplicate epoch triggers no oracle call and keeps both cache and history. -/
private theorem idealAdaptiveHandler_used
    [DecidableEq H] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (first : M) (answer : Option (Signature R H h v))
    (hused : history epoch = some (first, answer)) :
    (idealAdaptiveHandler hash enc projection budget core (Sum.inr (epoch, message))).run
      (history, cache) = pure (none, (history, cache)) := by
  change (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (SyncSignatureUnforgeability.signingOracle
        (oracleScheme hash enc projection budget) core (epoch, message) history)).run cache = _
  rw [SyncSignatureUnforgeability.signingOracle_used
    (oracleScheme hash enc projection budget) core history epoch message first answer hused]
  simp

private theorem genericFixedHandler_used [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (first : M) (answer : Option (Signature R H h v))
    (hused : history epoch = some (first, answer)) :
    (genericFixedHandler hash enc budget sk (Sum.inr (epoch, message))).run history =
      pure (none, history) := by
  change SyncSignatureUnforgeability.signingOracle
    (GXMSS.scheme hash enc budget) sk (epoch, message) history = _
  exact SyncSignatureUnforgeability.signingOracle_used
    (GXMSS.scheme hash enc budget) sk history epoch message first answer hused

/-- An unused epoch runs one ideal signing computation and records its optional answer. -/
private theorem idealAdaptiveHandler_unused
    [DecidableEq H] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hunused : history epoch = none) :
    (idealAdaptiveHandler hash enc projection budget core (Sum.inr (epoch, message))).run
      (history, cache) =
    (fun result => (result.1,
      (Function.update history epoch (some (message, result.1)), result.2))) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (oracleSign hash enc projection budget core epoch message)).run cache := by
  change (fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (SyncSignatureUnforgeability.signingOracle
        (oracleScheme hash enc projection budget) core (epoch, message) history)).run cache = _
  rw [SyncSignatureUnforgeability.signingOracle_unused
    (oracleScheme hash enc projection budget) core history epoch message hunused]
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]
  simp only [Functor.map_map]
  rfl

private theorem genericFixedHandler_unused [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (hunused : history epoch = none) :
    (genericFixedHandler hash enc budget sk (Sum.inr (epoch, message))).run history =
    (fun answer => (answer, Function.update history epoch (some (message, answer)))) <$>
      GXMSS.sign hash enc budget sk epoch message := by
  change SyncSignatureUnforgeability.signingOracle
    (GXMSS.scheme hash enc budget) sk (epoch, message) history = _
  rw [SyncSignatureUnforgeability.signingOracle_unused
    (GXMSS.scheme hash enc budget) sk history epoch message hunused]
  simp [GXMSS.scheme, map_eq_bind_pure_comp]
  rfl

private theorem projected_history_update_map
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (epoch : Fin (2 ^ h)) (message : M)
    (computation : ProbComp (Option (Signature R H h v) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)) :
    Prod.map id Prod.fst <$>
      ((fun result => (result.1,
        (Function.update history epoch (some (message, result.1)), result.2))) <$>
        computation) =
    (fun result => (result.1,
      Function.update history epoch (some (message, result.1)))) <$> computation := by
  simp [Functor.map_map, Prod.map]

private theorem mem_support_history_update_map
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (epoch : Fin (2 ^ h)) (message : M)
    (computation : ProbComp (Option (Signature R H h v) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache))
    (result : Option (Signature R H h v) ×
      (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v) ×
        ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache))
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

/-- A fixed related cache state gives the same one-query answer/history law as
the generic GXMSS signer. The local retry law compares eager and recursive draws. -/
private theorem idealAdaptiveHandler_projected
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache) :
    (Prod.map id Prod.fst <$> (idealAdaptiveHandler hash enc projection budget
      (GXMSS.keys hash pp starts).2 query).run
      (history, cache)) =ᵈ
    (genericFixedHandler hash enc budget (GXMSS.keys hash pp starts).2 query).run
      history := by
  cases query with
  | inl q =>
      rw [idealAdaptiveHandler_uniform, genericFixedHandler_uniform]
      simp [Functor.map_map]
  | inr q =>
      rcases q with ⟨epoch, message⟩
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [idealAdaptiveHandler_used hash enc projection budget
            (GXMSS.keys hash pp starts).2 epoch message
            history cache first answer hused]
          rw [genericFixedHandler_used hash enc budget
            (GXMSS.keys hash pp starts).2 epoch message history first answer hused]
          simp
      | none =>
          have hsign :
              (simulateQ (PRFScheme.prfIdealQueryImpl
                (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
                (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
                  epoch message)).run' cache =ᵈ
              GXMSS.sign hash enc budget (GXMSS.keys hash pp starts).2 epoch message := by
            rw [oracleSign_ideal_output hash enc projection budget epoch message
              pp starts history cache hcache hused]
            let : MeasurableSpace (Option (Signature R H h v)) := ⊤
            exact EvalDistEq.of_evalDist_eq
              (retry_sampling_sign hash enc projection budget hretry
                (GXMSS.keys hash pp starts).2 epoch message)
          rw [idealAdaptiveHandler_unused hash enc projection budget
            (GXMSS.keys hash pp starts).2 epoch message
            history cache hused]
          rw [genericFixedHandler_unused hash enc budget
            (GXMSS.keys hash pp starts).2 epoch message history hused]
          calc
            _ = (fun result => (result.1,
                Function.update history epoch (some (message, result.1)))) <$>
                (simulateQ (PRFScheme.prfIdealQueryImpl
                  (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
                  (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
                    epoch message)).run cache := by
                    exact projected_history_update_map history epoch message _
            _ =ᵈ _ := by
              simpa only [StateT.run'_eq, Functor.map_map] using
                hsign.map (fun answer =>
                  (answer, Function.update history epoch (some (message, answer))))

/-- The cache relation is closed under every adversary oracle step. -/
private theorem idealAdaptiveHandler_preserves
    [DecidableEq H] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache)
    (result : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Range query ×
        ((SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
          (Signature R H h v)) ×
          ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache))
    (hresult : result ∈ support ((idealAdaptiveHandler hash enc projection budget
      (GXMSS.keys hash pp starts).2 query).run
      (history, cache))) :
    let next := result.2
    RetryFresh (H := H) (R := R) pp next.1 next.2 := by
  cases query with
  | inl q =>
      rw [idealAdaptiveHandler_uniform] at hresult
      rw [support_map] at hresult
      obtain ⟨response, _, heq⟩ := hresult
      subst result
      exact hcache
  | inr q =>
      rcases q with ⟨epoch, message⟩
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [idealAdaptiveHandler_used hash enc projection budget
            (GXMSS.keys hash pp starts).2 epoch message
            history cache first answer hused] at hresult
          simp only [support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hcache
      | none =>
          rw [idealAdaptiveHandler_unused hash enc projection budget
            (GXMSS.keys hash pp starts).2 epoch message
            history cache hused] at hresult
          obtain ⟨signed, hsigned, heq⟩ :=
            mem_support_history_update_map history epoch message _ result hresult
          subst result
          exact oracleSign_ideal_preserves hash enc projection budget epoch message
            pp starts history cache hcache signed hsigned

/-- One related cache/history state couples every oracle answer to the generic
scheme while retaining the relation for subsequent adaptive queries. -/
private theorem idealAdaptiveHandler_rel
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (left : (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (right : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (hrel : CacheRelated pp left right) :
    RelTriple
      ((idealAdaptiveHandler hash enc projection budget
        (GXMSS.keys hash pp starts).2 query).run left)
      ((genericFixedHandler hash enc budget (GXMSS.keys hash pp starts).2 query).run
        right)
      (fun a b => a.1 = b.1 ∧ CacheRelated pp a.2 b.2) := by
  rcases left with ⟨history, cache⟩
  obtain ⟨rfl, hcache⟩ := hrel
  apply relTriple_of_projected_eq _ _ Prod.fst (CacheRelated pp)
  · exact idealAdaptiveHandler_projected hash enc projection budget hretry pp starts
      query history cache hcache
  · intro result hresult
    exact ⟨rfl, idealAdaptiveHandler_preserves hash enc projection budget pp starts
      query history cache hcache result hresult⟩

/-- For any adaptive source program, the cached ideal function and generic signer
give the same forgery and first-request history from related states. -/
private theorem idealAdaptiveRun_projected {A : Type}
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (program : OracleComp
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v)) A)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache) :
    (Prod.map id Prod.fst <$>
      (simulateQ (idealAdaptiveHandler hash enc projection budget
        (GXMSS.keys hash pp starts).2) program).run
        (history, cache)) =ᵈ
      (simulateQ (genericFixedHandler hash enc budget (GXMSS.keys hash pp starts).2)
        program).run history := by
  have hrel := relTriple_simulateQ_run
    (idealAdaptiveHandler hash enc projection budget (GXMSS.keys hash pp starts).2)
    (genericFixedHandler hash enc budget (GXMSS.keys hash pp starts).2)
    (CacheRelated pp) program
    (idealAdaptiveHandler_rel hash enc projection budget hretry pp starts)
    (history, cache) history ⟨rfl, hcache⟩
  have hmap := evalDistEq_map_of_relTriple
    (f := Prod.map id Prod.fst) (g := id) (by
      apply relTriple_post_mono hrel
      intro left right h
      rcases h with ⟨hresponse, hstate⟩
      exact Prod.ext hresponse hstate.1)
  simpa only [id_map] using hmap

/-- Two-stage cached-ideal interpretation is the same combined handler. -/
private theorem idealAdaptiveHandler_compose {A : Type} [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (program : OracleComp
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v)) A)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      ((simulateQ (adaptiveHandler hash enc projection budget core) program).run
        history)).run cache =
    (fun result : A × _ × _ =>
      let next := result.2
      ((result.1, next.1), next.2)) <$>
      (simulateQ (idealAdaptiveHandler hash enc projection budget core) program).run
        (history, cache) := by
  apply simulateQ_StateT_StateT_compose
    (adaptiveHandler hash enc projection budget core)
    (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
    (idealAdaptiveHandler hash enc projection budget core)
  intro query state retained
  change _ = (fun result =>
      let next := result.2
      ((result.1, next.1), next.2)) <$>
    ((fun ⟨⟨answer, nextHistory⟩, nextCache⟩ =>
      (answer, (nextHistory, nextCache))) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        ((adaptiveHandler hash enc projection budget core query).run state)).run retained)
  simp only [Functor.map_map]
  have hfun : (fun result :
      ((unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v)).Range query ×
        SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
          (Signature R H h v)) ×
        ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache =>
      let pair := result.1
      ((pair.1, pair.2), result.2)) = id := by
    funext result
    rcases result with ⟨⟨answer, nextHistory⟩, nextCache⟩
    rfl
  rw [hfun, id_map]

/-- One full adaptive interaction under the shared function oracle. -/
@[expose] def adaptiveInteraction [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (SyncSignatureUnforgeability.ExperimentResult
        (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := do
  let pp ← publicSeedQuery projection
  let starts ← startQueries projection pp
  let pair := GXMSS.keys hash pp starts
  let pk := pair.1
  let (forgery, history) ←
    (simulateQ (adaptiveHandler hash enc projection budget pair.2) (adv.forge pk)).run
      SyncSignatureUnforgeability.emptyHistory
  pure (pk, forgery, history)

/-- The reduction key generator retains its complete signing core locally. -/
private theorem adaptiveInteraction_from_material [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    adaptiveInteraction hash enc projection budget adv = (do
      let material ← keyMaterialQueries projection
      let pair := GXMSS.keys hash material.1 material.2
      let outcome ←
        (simulateQ (adaptiveHandler hash enc projection budget pair.2)
          (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome.1, outcome.2)) := by
  simp [adaptiveInteraction, keyMaterialQueries, bind_assoc]

/-- A Boolean observation of the full shared-oracle interaction. -/
@[expose] def randgenPRFReduction [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    : PRFScheme.PRFAdversary (GXMSS.PRFDerived.Query PP M h v) Response :=
  let alg := oracleScheme hash enc projection budget
  let run := adaptiveInteraction hash enc projection budget adv
  run.map (SyncSignatureUnforgeability.strongValid alg)

/-- Expose the initial ideal key material and retained cache before running the
adversary's complete adaptive signing interaction. -/
private theorem ideal_adaptive_interaction_setup [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc projection budget adv)).run' ∅ =
    (do
      let initial ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (keyMaterialQueries projection)).run ∅
      let material := initial.1
      let pk := (GXMSS.keys hash material.1 material.2).1
      let outcome ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        ((simulateQ (adaptiveHandler hash enc projection budget
          (GXMSS.keys hash material.1 material.2).2)
          (adv.forge pk)).run SyncSignatureUnforgeability.emptyHistory)).run'
          initial.2
      pure (pk, outcome)) := by
  rw [adaptiveInteraction_from_material]
  rw [simulateQ_bind, StateT.run'_bind']
  apply bind_congr
  intro initial
  rcases initial with ⟨⟨pp, starts⟩, cache⟩
  simp only [Prod.mk.eta, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  intro result
  rfl

/-- A related initial cache lets the full ideal adaptive run project to one
generic GXMSS signing history. -/
private theorem ideal_adaptive_fixed_coupling
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp
      SyncSignatureUnforgeability.emptyHistory cache)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      ((simulateQ (adaptiveHandler hash enc projection budget
        (GXMSS.keys hash pp starts).2)
        (adv.forge (GXMSS.keys hash pp starts).1)).run
          SyncSignatureUnforgeability.emptyHistory)).run' cache =ᵈ
    (simulateQ (genericFixedHandler hash enc budget
      (GXMSS.keys hash pp starts).2)
      (adv.forge (GXMSS.keys hash pp starts).1)).run
        SyncSignatureUnforgeability.emptyHistory := by
  rw [StateT.run'_eq]
  rw [idealAdaptiveHandler_compose]
  have hbridge := idealAdaptiveRun_projected hash enc projection budget hretry
    pp starts (adv.forge (GXMSS.keys hash pp starts).1)
    SyncSignatureUnforgeability.emptyHistory cache hcache
  simp only [Functor.map_map]
  convert hbridge using 1
  congr 1

/-- Generic key generation exposes the same seed/start material before the
synchronized adversary and signer run. -/
private theorem generic_interaction_material [SampleableType H]
    [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.interaction (GXMSS.scheme hash enc budget) adv =
    (do
      let pp ← hash.thf.seedGen
      let starts ← GXMSS.sampleStarts H h v
      let pair := GXMSS.keys hash pp starts
      let outcome ← (simulateQ (genericFixedHandler hash enc budget pair.2)
        (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome)) := by
  unfold SyncSignatureUnforgeability.interaction GXMSS.scheme GXMSS.keygen
  simp only [bind_assoc, pure_bind]
  rfl

/-- The one-cache ideal PRF experiment and generic GXMSS have the same full
adaptive interaction law, including the forgery and consumed-epoch history. -/
private theorem ideal_adaptive_interaction_correspondence [SampleableType H]
    [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    letI : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
    𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc projection budget adv)).run' ∅] =
    𝒟[SyncSignatureUnforgeability.interaction
      (GXMSS.scheme hash enc budget) adv] := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (PP × (Fin (2 ^ h) → Fin v → H)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  let setup := (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries projection)).run
  let follow : (PP × (Fin (2 ^ h) → Fin v → H)) →
      ProbComp (SyncSignatureUnforgeability.ExperimentResult
        (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :=
    fun material => do
      let pair := GXMSS.keys hash material.1 material.2
      let outcome ← (simulateQ (genericFixedHandler hash enc budget pair.2)
        (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome)
  rw [ideal_adaptive_interaction_setup, generic_interaction_material]
  calc
    _ = 𝒟[do
      let initial ← setup ∅
      follow initial.1] := by
        apply OracleComp.evalDist_bind_congr_of_support
        intro initial hinitial
        rcases initial with ⟨⟨pp, starts⟩, cache⟩
        have hcache := keyMaterial_ideal_cache projection
          ((pp, starts), cache) hinitial
        have hfixed := ideal_adaptive_fixed_coupling hash enc projection budget
          hretry pp starts cache hcache adv
        convert (hfixed.map fun outcome =>
          (show SyncSignatureUnforgeability.ExperimentResult
            (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v) from
            ((GXMSS.keys hash pp starts).1, outcome))).evalDist_eq using 1 <;>
          (unfold SyncSignatureUnforgeability.ExperimentResult at *
           simp [follow, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
           rfl)
    _ = 𝒟[do
      let material ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (keyMaterialQueries projection)).run' ∅
      follow material] := by
        change 𝒟[setup ∅ >>= fun initial => follow initial.1] =
          𝒟[(Prod.fst <$> setup ∅) >>= follow]
        rw [bind_map_left]
    _ = 𝒟[do
      let material ← (do
        let pp ← hash.thf.seedGen
        let starts ← GXMSS.sampleStarts H h v
        pure (pp, starts))
      follow material] := by
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
          keyMaterial_ideal_sampling hash projection hseed hstart]
    _ = _ := by
      simp [follow, bind_assoc]


end GXMSS.PRFDerived.Unforgeability

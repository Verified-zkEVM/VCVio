/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerived.OracleQueries
public import VCVio.CryptoFoundations.SyncSignatureAlg.PRFSimulation

/-!
# Shared-response interval PRF reduction

The adaptive reduction uses the common first-request signing handler. Its real interpretation
retains actual evaluator-key generation and every returned strong-unforgeability observation.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding ENNReal GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory
open OracleComp.ProgramLogic.Relational
open PRFScheme.QuerySimulation PRFScheme.ProjectedQueries
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- An active request queries the whole retry budget; an inactive request has no function calls. -/
@[expose] def oracleSign (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (core : GXMSS.Interval.SecretKey PP H h v I)
    (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (Option (Signature R H h v)) :=
  if Epoch.IsActive I epoch then do
    let complete := core.complete
    let randomizers ← retryQueries projection budget complete.seed epoch message
    pure (GXMSS.Interval.PRFDerived.signResult hash enc I core epoch message randomizers).output
  else pure none

private theorem oracleSign_bound (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (I : Interval h) (core : GXMSS.Interval.SecretKey PP H h v I)
    (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (oracleSign hash enc p budget I core epoch message) budget := by
  let complete := core.complete
  unfold oracleSign
  split
  · simpa only [Nat.add_zero] using isTotalQueryBound_bind
      (retryQueries_bound p budget complete.seed epoch message)
      (fun randomizers => (show IsTotalQueryBound (pure
        (GXMSS.Interval.PRFDerived.signResult hash enc I core epoch message randomizers).output :
          OracleComp (PRFScheme.PRFOracleSpec
            (GXMSS.Interval.PRFDerived.Query PP M h v) Response) _) 0 from trivial))
  · trivial

/-- The synchronized interval scheme over the shared function oracle, with captured interval
and retry budget. -/
@[expose] noncomputable def oracleScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) :
    SyncSignatureAlg
      (OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response))
      M (PublicKey PP H) (GXMSS.Interval.SecretKey PP H h v I)
        (Signature R H h v) (Fin (2 ^ h)) where
  keygen := do
    let pp ← publicSeedQuery projection
    let starts ← startQueries I projection pp
    let fillers ← fillerQueries I projection pp
    pure (GXMSS.Interval.keys hash I pp starts fillers)
  sign := oracleSign hash enc projection budget I
  verify := GXMSS.verify hash enc

/-- The source adversary's uniform oracle is forwarded and its signing oracle
uses the shared function interface. A duplicate epoch invokes neither function queries
nor signing and leaves the first-request history unchanged. -/
@[expose] noncomputable def adaptiveHandler [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (core : GXMSS.Interval.SecretKey PP H h v I) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v))
        (OracleComp (PRFScheme.PRFOracleSpec
          (GXMSS.Interval.PRFDerived.Query PP M h v) Response))) :=
  SyncSignatureUnforgeability.PRFSimulation.signingHandler
    (oracleScheme hash enc projection budget I) core

/-- Ambient sampling makes no function calls; an eligible signing query makes
exactly its retry budget, including all prefetched draws. -/
private theorem adaptiveHandler_query_bound [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (core : GXMSS.Interval.SecretKey PP H h v I)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    IsQueryBoundP ((adaptiveHandler hash enc projection budget I core query).run history)
      (fun q => q.isRight = true)
      (if query.isRight then budget else 0) := by
  exact SyncSignatureUnforgeability.PRFSimulation.signingHandler_query_bound
    (oracleScheme hash enc projection budget I) core budget
    (oracleSign_bound hash enc projection budget I core) query history

/-- The ideal function cache and synchronized signing history as one state machine. -/
@[expose] noncomputable def adaptiveInteraction [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (SyncSignatureUnforgeability.ExperimentResult
        (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := do
  let pp ← publicSeedQuery projection
  let starts ← startQueries I projection pp
  let fillers ← fillerQueries I projection pp
  let pair := GXMSS.Interval.keys hash I pp starts fillers
  let pk := pair.1
  (fun outcome => (pk, outcome.1, outcome.2)) <$>
    (simulateQ (adaptiveHandler hash enc projection budget I pair.2) (adv.forge pk)).run
      SyncSignatureUnforgeability.emptyHistory

/-- The reduction key generator retains its complete signing core locally. -/
private theorem adaptiveInteraction_from_material [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    adaptiveInteraction hash enc projection budget I adv = (do
      let material ← keyMaterialQueries I projection
      let (pp, starts, fillers) := material
      let pair := GXMSS.Interval.keys hash I pp starts fillers
      let outcome ←
        (simulateQ (adaptiveHandler hash enc projection budget I pair.2)
          (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome.1, outcome.2)) := by
  unfold adaptiveInteraction keyMaterialQueries
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  apply bind_congr
  intro fillers
  -- Setup has exposed the semireducible ExperimentResult triple.
  erw [map_eq_bind_pure_comp]
  rfl

/-- A Boolean observation of the full shared-oracle interaction. -/
@[expose] noncomputable def randgenPRFReduction [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    : PRFScheme.PRFAdversary (GXMSS.Interval.PRFDerived.Query PP M h v) Response :=
  let alg := oracleScheme hash enc projection budget I
  let run := adaptiveInteraction hash enc projection budget I adv
  run.map (SyncSignatureUnforgeability.strongValid alg)

/-- Real oracle signing from the reduction's retained core agrees with
recomputation by the seed-only scheme for the same evaluator key. -/
private theorem oracleSign_real
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (key : Key) (budget : ℕ) (I : Interval h) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (oracleSign hash enc projection budget I
        (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key)
        epoch message) =
    GXMSS.Interval.PRFDerived.sign hash enc prf.eval projection budget I
                key epoch message := by
  unfold oracleSign GXMSS.Interval.PRFDerived.sign GXMSS.Interval.PRFDerived.run
  by_cases he : Epoch.IsActive I epoch
  · simp only [ite_eq_left he, simulateQ_bind]
    rw [retryQueries_real]
    rfl
  · simp [he, GXMSS.PRFDerived.SigningTransition.output,
      VCVio.Algorithms.FirstSuccess.Result.output]

/-- The source scheme with its sampled evaluator key fixed for one interaction. -/
private def fixedKeyScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (key : Key) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) Key
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := pure (GXMSS.Interval.PRFDerived.keys hash I prf.eval projection key)
  sign := GXMSS.Interval.PRFDerived.sign hash enc prf.eval projection budget I
  verify := GXMSS.verify hash enc

/-- The ordinary synchronized source handler for a fixed evaluator key. -/
private def fixedKeyHandler [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (key : Key) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp) :=
  SyncSignatureUnforgeability.PRFSimulation.fixedHandler
    (fixedKeyScheme hash enc prf projection budget I key) key

/-- Per-query real simulation preserves the synchronized history, including failed
answers and already consumed epochs. -/
private theorem adaptiveHandler_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (key : Key)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      ((adaptiveHandler hash enc projection budget I
        (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key)
        query).run history) =
    (fixedKeyHandler hash enc prf projection budget I key query).run history := by
  cases query with
  | inl q =>
      simp [adaptiveHandler, SyncSignatureUnforgeability.PRFSimulation.signingHandler,
        fixedKeyHandler, SyncSignatureUnforgeability.PRFSimulation.fixedHandler,
        PRFScheme.prfRealQueryImpl,
        QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
  | inr q =>
      rcases q with ⟨epoch, message⟩
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          simp only [adaptiveHandler, SyncSignatureUnforgeability.PRFSimulation.signingHandler,
            fixedKeyHandler, SyncSignatureUnforgeability.PRFSimulation.fixedHandler,
            QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget I)
                  (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget I key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused),
            SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          simp
      | none =>
          simp only [adaptiveHandler, SyncSignatureUnforgeability.PRFSimulation.signingHandler,
            fixedKeyHandler, SyncSignatureUnforgeability.PRFSimulation.fixedHandler,
            QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget I)
                  (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget I key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused),
            SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          simp only [simulateQ_bind, simulateQ_pure]
          change (do
            let answer ← simulateQ (prf.prfRealQueryImpl key)
              (oracleSign hash enc projection budget I
                (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key)
                epoch message)
            pure (answer, Function.update history epoch (some (message, answer)))) =
            (do
              let answer ← GXMSS.Interval.PRFDerived.sign hash enc prf.eval projection budget I
                key epoch message
              pure (answer, Function.update history epoch (some (message, answer))))
          rw [oracleSign_real]

/-- The real oracle program has exactly the fixed-key synchronized interaction,
including its complete returned-failure and freshness observation. -/
private theorem adaptiveInteraction_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (key : Key)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      (adaptiveInteraction hash enc projection budget I adv) =
    SyncSignatureUnforgeability.interaction
      (fixedKeyScheme hash enc prf projection budget I key) adv := by
  unfold adaptiveInteraction
  rw [simulateQ_bind]
  simp only [publicSeedQuery, simulateQ_map,
    PRFScheme.simulateQ_prfRealQueryImpl_functionQuery, map_pure, pure_bind]
  rw [simulateQ_bind, startQueries_real]
  simp only [pure_bind]
  rw [simulateQ_bind, fillerQueries_real]
  simp only [pure_bind]
  -- The concrete result tuple must unfold ExperimentResult when transporting the map.
  erw [simulateQ_map]
  have hcomp := simulateQ_StateT_compose
    (adaptiveHandler hash enc projection budget I
      (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key))
    (prf.prfRealQueryImpl key)
    (fixedKeyHandler hash enc prf projection budget I key)
    (adaptiveHandler_real hash enc prf projection budget I key)
    (adv.forge (GXMSS.Interval.PRFDerived.keys hash I prf.eval projection key).1)
    SyncSignatureUnforgeability.emptyHistory
  change (fun outcome =>
    ((GXMSS.Interval.PRFDerived.keys hash I prf.eval projection key).1,
      outcome.1, outcome.2)) <$>
      simulateQ (prf.prfRealQueryImpl key)
        ((simulateQ (adaptiveHandler hash enc projection budget I
          (GXMSS.Interval.PRFDerived.transientCore hash I prf.eval projection key))
          (adv.forge (GXMSS.Interval.PRFDerived.keys hash I prf.eval projection key).1)).run
            SyncSignatureUnforgeability.emptyHistory) = _
  rw [hcomp]
  unfold SyncSignatureUnforgeability.interaction fixedKeyScheme fixedKeyHandler
    SyncSignatureUnforgeability.PRFSimulation.fixedHandler
  simp only [pure_bind]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The real PRF distinguisher observes the complete strong synchronized game.
The same runtime interpretation therefore preserves missing mass as well as returned failure. -/
theorem randgenPRFReduction_real_strong [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfRealExperiment (randgenPRFReduction hash enc projection budget I adv) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
          adv := by
  unfold PRFScheme.prfRealExperiment randgenPRFReduction
  change (do
    let key ← prf.keygen
    simulateQ (prf.prfRealQueryImpl key)
      ((SyncSignatureUnforgeability.strongValid
        (oracleScheme hash enc projection budget I)) <$>
        adaptiveInteraction hash enc projection budget I adv)) = _
  simp only [simulateQ_map, adaptiveInteraction_real]
  unfold SyncSignatureUnforgeability.interaction GXMSS.Interval.PRFDerived.scheme
    GXMSS.Interval.PRFDerived.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro key
  rfl

/-- All adversarial signing requests give the displayed pathwise function-query bound. -/
theorem randgenPRFReduction_functionQuery_bound [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : SyncSignatureUnforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc projection budget I adv)
      (fun query => query.isRight = true)
      (functionQueryCount I v qs budget) := by
  unfold functionQueryCount
  unfold randgenPRFReduction
  apply (isQueryBoundP_map_iff _ _ _).mpr
  rw [adaptiveInteraction_from_material]
  apply isQueryBoundP_bind
    (p := fun query => query.isRight = true)
    (keyMaterialQueries_bound (M := M) I projection).isQueryBoundP
  intro material _
  rcases material with ⟨pp, starts, fillers⟩
  let pair := GXMSS.Interval.keys hash I pp starts fillers
  have hrun : IsQueryBoundP
      ((simulateQ (adaptiveHandler hash enc projection budget I pair.2)
        (adv.forge pair.1)).run
        SyncSignatureUnforgeability.emptyHistory)
      (fun query => query.isRight = true)
      (qs * budget) := by
    apply (hbound pair.1).simulateQ_run_of_step_le
      (cost := budget) (impl := adaptiveHandler hash enc projection budget I pair.2)
    · intro query hp history
      change query.isRight = true at hp
      simpa only [hp, ite_true] using
        adaptiveHandler_query_bound hash enc projection budget I pair.2 query history
    · intro query hp history
      change ¬ query.isRight = true at hp
      simpa only [ite_eq_right hp] using
        adaptiveHandler_query_bound hash enc projection budget I pair.2 query history
  have hresult : IsQueryBoundP
      (do
        let result ← (simulateQ (adaptiveHandler hash enc projection budget I pair.2)
          (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
        pure (pair.1, result.1, result.2))
      (fun query => query.isRight = true)
      (qs * budget) := by
    simpa only [Nat.add_zero] using isQueryBoundP_bind hrun
      (fun result _ => (show IsQueryBoundP
        (pure (pair.1, result.1, result.2) : OracleComp
          (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response) _)
        (fun query => query.isRight = true) 0 from trivial))
  exact hresult


end GXMSS.Interval.PRFDerived.Unforgeability

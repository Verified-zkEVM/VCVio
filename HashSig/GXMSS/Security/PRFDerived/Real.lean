/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.Interaction
import all HashSig.GXMSS.Security.PRFDerived.KeyMaterial
import all HashSig.GXMSS.Security.PRFDerived.Signing
import all HashSig.GXMSS.Security.PRFDerived.Interaction

/-!
# Real-oracle correspondence for PRF-derived GXMSS

The real PRF handler agrees with the seed-only scheme throughout the synchronized interaction,
including returned failure, consumed epochs, and the exact strong-freshness observation.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The real PRF handler supplies precisely the deterministic retry sequence. -/
private theorem retryQueries_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (key : Key) (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (retryQueries projection budget pp epoch message) =
    pure (GXMSS.PRFDerived.retryRandomizers budget prf.eval projection
      key pp epoch message) := by
  unfold retryQueries
  change simulateQ (prf.prfRealQueryImpl key)
    (List.ofFn <$> Fin.mOfFn budget (fun attempt => projection.retryRandomizer <$>
      PRFScheme.functionQuery (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val))) = _
  rw [simulateQ_map]
  have hflat : simulateQ (prf.prfRealQueryImpl key)
      (Fin.mOfFn budget fun attempt => projection.retryRandomizer <$>
        PRFScheme.functionQuery (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val)) =
      pure (fun attempt : Fin budget => projection.retryRandomizer
        (prf.eval key (.retry pp epoch message attempt.val))) := by
    apply simulateQ_fin_mOfFn_pure
    intro attempt
    simp
  rw [hflat]
  rfl

/-- Real oracle signing from the reduction's retained core agrees with
recomputation by the seed-only scheme for the same evaluator key. -/
private theorem oracleSign_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (key : Key) (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (oracleSign hash enc projection budget
        (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
        epoch message) =
    GXMSS.PRFDerived.sign budget prf.eval projection hash enc key epoch message := by
  unfold oracleSign
  rw [simulateQ_bind]
  rw [retryQueries_real]
  rfl

/-- The source scheme with its sampled evaluator key fixed for one interaction. -/
private def fixedKeyScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (key : Key) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) Key
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := pure (GXMSS.PRFDerived.keys hash prf.eval projection key)
  sign := GXMSS.PRFDerived.sign budget prf.eval projection hash enc
  verify := GXMSS.verify hash enc

/-- The ordinary synchronized source handler for a fixed evaluator key. -/
private def fixedKeyHandler [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (key : Key) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle
      (fixedKeyScheme hash enc prf projection budget key) key

/-- Per-query real simulation preserves the synchronized history, including failed
answers and already consumed epochs. -/
private theorem adaptiveHandler_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (key : Key)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      ((adaptiveHandler hash enc projection budget
        (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
        query).run history) =
    (fixedKeyHandler hash enc prf projection budget key query).run history := by
  cases query with
  | inl q =>
      simp [adaptiveHandler, fixedKeyHandler, PRFScheme.prfRealQueryImpl,
        QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
  | inr q =>
      rcases q with ⟨epoch, message⟩
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          simp only [adaptiveHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget)
                  (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused),
            SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          simp
      | none =>
          simp only [adaptiveHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget)
                  (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused),
            SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          simp only [simulateQ_bind, simulateQ_pure]
          change (do
            let answer ← simulateQ (prf.prfRealQueryImpl key)
              (oracleSign hash enc projection budget
                (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                epoch message)
            pure (answer, Function.update history epoch (some (message, answer)))) =
            (do
              let answer ← GXMSS.PRFDerived.sign budget prf.eval projection
                hash enc key epoch message
              pure (answer, Function.update history epoch (some (message, answer))))
          rw [oracleSign_real]

/-- The real oracle program has exactly the fixed-key synchronized interaction,
including its complete returned-failure and freshness observation. -/
private theorem adaptiveInteraction_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (key : Key)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      (adaptiveInteraction hash enc projection budget adv) =
    SyncSignatureUnforgeability.interaction
      (fixedKeyScheme hash enc prf projection budget key) adv := by
  unfold adaptiveInteraction
  rw [simulateQ_bind]
  simp only [publicSeedQuery, simulateQ_map,
    PRFScheme.simulateQ_prfRealQueryImpl_functionQuery, map_pure, pure_bind]
  rw [simulateQ_bind, startQueries_real]
  simp only [pure_bind]
  rw [simulateQ_bind]
  have hcomp := simulateQ_StateT_compose
    (adaptiveHandler hash enc projection budget
      (GXMSS.PRFDerived.transientCore hash prf.eval projection key))
    (prf.prfRealQueryImpl key)
    (fixedKeyHandler hash enc prf projection budget key)
    (adaptiveHandler_real hash enc prf projection budget key)
    (adv.forge (GXMSS.PRFDerived.keys hash prf.eval projection key).1)
    SyncSignatureUnforgeability.emptyHistory
  dsimp [GXMSS.PRFDerived.transientCore, GXMSS.PRFDerived.keys,
    GXMSS.PRFDerived.publicSeed, GXMSS.PRFDerived.starts] at hcomp
  unfold GXMSS.PRFDerived.starts at hcomp
  rw [hcomp]
  rfl

/-- The real PRF distinguisher observes the complete strong synchronized game.
The same runtime interpretation therefore preserves missing mass as well as returned failure. -/
theorem randgenPRFReduction_real_strong [SampleableType Key] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (keyLaw : prf.UniformKey) :
    prf.prfRealExperiment (randgenPRFReduction hash enc projection budget adv) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget) adv := by
  unfold PRFScheme.prfRealExperiment randgenPRFReduction
  rw [keyLaw]
  change (do
    let key ← $ᵗ Key
    simulateQ (prf.prfRealQueryImpl key)
      ((SyncSignatureUnforgeability.strongValid
        (oracleScheme hash enc projection budget)) <$>
        adaptiveInteraction hash enc projection budget adv)) = _
  simp only [simulateQ_map, adaptiveInteraction_real]
  unfold SyncSignatureUnforgeability.interaction GXMSS.PRFDerived.scheme
    GXMSS.PRFDerived.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro key
  rfl

end GXMSS.PRFDerived.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.PRFDerivedScheme
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.PRFDerived.KeyGeneration
import all HashSig.GXMSS.Security.PRFDerived.KeyGeneration
public import HashSig.GXMSS.Security.PRFDerived.KeyMaterial
import all HashSig.GXMSS.Security.PRFDerived.KeyMaterial
public import HashSig.GXMSS.Security.PRFDerived.OracleQueries
import all HashSig.GXMSS.Security.PRFDerived.OracleQueries
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
import all HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.SigningCoordinates
import all HashSig.GXMSS.Security.PRFDerived.SigningCoordinates
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation
import all HashSig.GXMSS.Security.PRFDerived.SigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Cached PRF signing simulation

Cached retry queries and fixed-key signing are coupled with their full state and failure
observations. The oracle scheme is independent of final security composition.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- For a fresh eligible epoch, signing uses the retained key material and the
disjoint retry inputs have their independent sampling law. -/
private theorem oracleSign_ideal_output
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache) (hunused : history epoch = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run' cache =
    (fun randomizers =>
      (GXMSS.PRFDerived.signResult hash enc (GXMSS.keys hash pp starts).2
        epoch message randomizers).output) <$>
      projectedRetries projection budget := by
  let ideal := PRFScheme.prfIdealQueryImpl
    (D := GXMSS.PRFDerived.Query PP M h v) (R := Response)
  have hfresh : ∀ attempt : Fin budget, cache (.retry pp epoch message attempt.val) = none :=
    fun attempt => hcache epoch hunused message attempt.val
  unfold oracleSign
  simp only [GXMSS.keys]
  rw [simulateQ_bind, StateT.run'_bind']
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure, bind_pure_comp]
  calc
    _ = (fun randomizers =>
        (GXMSS.PRFDerived.signResult hash enc
          ⟨pp, starts, GXMSS.endpoints hash pp starts⟩
          epoch message randomizers).output) <$>
        (simulateQ (PRFScheme.prfIdealQueryImpl
          (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
          (retryQueries projection budget pp epoch message)).run' cache := by
          simp [StateT.run'_eq, Functor.map_map]
    _ = _ := by
      simpa only [GXMSS.keys] using
        congrArg (fun draws => (fun randomizers =>
          (GXMSS.PRFDerived.signResult hash enc
            ⟨pp, starts, GXMSS.endpoints hash pp starts⟩
            epoch message randomizers).output) <$> draws)
          (retryQueries_ideal_fresh projection budget pp epoch message cache hfresh)

/-- The full cached-ideal signing state differs from the retry-draw state only by
the deterministic first-success output. -/
private theorem oracleSign_ideal_run_cached
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run cache =
    (fun result =>
      ((GXMSS.PRFDerived.signResult hash enc (GXMSS.keys hash pp starts).2
        epoch message result.1).output, result.2)) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (retryQueries projection budget pp epoch message)).run cache := by
  unfold oracleSign
  simp only [GXMSS.keys]
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- Every ideal signing outcome, including returned failure, retains the cache
relation for the updated consumed-epoch history. -/
private theorem oracleSign_ideal_preserves
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache) (result : Option (Signature R H h v) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run cache)) :
    RetryFresh (H := H) (R := R) pp
      (Function.update history epoch (some (message, result.1))) result.2 := by
  rw [oracleSign_ideal_run_cached hash enc projection budget epoch message
    pp starts cache, support_map] at hresult
  obtain ⟨retries, hretries, heq⟩ := hresult
  subst result
  exact retryQueries_preserve_retryFresh projection budget pp epoch message
    history _ cache retries hcache hretries

/-- One eligible signing call makes exactly its budgeted retry calls. -/
private theorem oracleSign_bound
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (core : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (oracleSign hash enc projection budget core epoch message)
      budget := by
  unfold oracleSign
  have hretry := retryQueries_bound (v := v) projection budget core.seed epoch message
  have hresult : ∀ randomizers, IsTotalQueryBound
        (pure (GXMSS.PRFDerived.signResult hash enc core
          epoch message randomizers).output : OracleComp
            (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response) _)
        0 := fun _ => trivial
  simpa only [Nat.add_zero] using isTotalQueryBound_bind hretry hresult

/-- The reduction retains the full signing core after its one key-generation
query sequence. The actual PRF-derived scheme retains only its evaluator key. -/
@[expose] def oracleScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
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
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
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

end GXMSS.PRFDerived.Unforgeability

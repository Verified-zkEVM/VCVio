/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerived.Scheme
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Interval.PRFDerived.Scheme
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
import all HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation
import all HashSig.GXMSS.Security.PRFDerived.SigningSimulation
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Shared-response interval PRF reduction

Setup queries only active starts and maximal inactive roots. The named adaptive reduction
preserves the signing history, forwards ambient randomness and caches full responses.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec Encoding ENNReal GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- One keyed PRF supplies every query family through a common abstract response. -/
abbrev SharedPRF (Key PP M Response : Type) (h v : ℕ) :=
  PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response

/-- The distinguished response has exactly the THF public-seed sampling law. -/
@[expose] def PublicSeedSamplingLaw [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace PP := ⊤
  𝒟[projection.publicParameter <$> ($ᵗ Response)] =
    𝒟[(HashInstance.thf hash).seedGen]

/-- Each distinct chain-start response projects to the canonical uniform start law. -/
@[expose] def ChainStartSamplingLaw [SampleableType Response] [SampleableType H]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace H := ⊤
  𝒟[projection.chainStart <$> ($ᵗ Response)] = 𝒟[$ᵗ H]

/-- A function-oracle query for the public parameter. -/
@[expose] def publicSeedQuery
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v)
      Response) PP :=
  projection.publicParameter <$> PRFScheme.functionQuery .publicSeed

/-- A function-oracle query for one start under the derived public parameter. -/
@[expose] def startQuery
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v)
      Response) H :=
  projection.chainStart <$> PRFScheme.functionQuery (.start pp epoch chain)

/-- Setup queries one start per active epoch and chain, with a deterministic inactive extension. -/
@[expose] def startQueries (I : Interval h)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (Fin (2 ^ h) → Fin v → H) :=
  (fun flat => GXMSS.Interval.PRFDerived.extendStarts I
    (fun i chain => flat (finProdFinEquiv (i, chain)))) <$>
      Fin.mOfFn ((I.last.val - I.first.val + 1) * v) (fun index =>
        startQuery projection pp (GXMSS.Interval.PRFDerived.activeEpoch I index.divNat)
          index.modNat)

/-- A frontier query uses its level and index, without serializing the interval. -/
@[expose] def fillerQuery
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    {I : Interval h} (node : Subtree.FrontierNode I) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response) H :=
  let (level, index) := node.val
  projection.fillerDigest <$> PRFScheme.functionQuery (.filler pp level index)

/-- Enumerate exactly the maximal inactive frontier. -/
@[expose] noncomputable def fillerQueries (I : Interval h)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (Fillers I H) :=
  (fun flat node => flat (Fintype.equivFin (Subtree.FrontierNode I) node)) <$>
    Fin.mOfFn (Fintype.card (Subtree.FrontierNode I)) (fun i =>
      fillerQuery projection pp ((Fintype.equivFin (Subtree.FrontierNode I)).symm i))

/-- Frontier response projection has the canonical uniform digest law. -/
@[expose] def FillerSamplingLaw [SampleableType Response] [SampleableType H]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace H := ⊤
  𝒟[projection.fillerDigest <$> ($ᵗ Response)] = 𝒟[$ᵗ H]

private theorem publicSeedQuery_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (publicSeedQuery (M := M) (h := h) (v := v) projection) 1 := by
  unfold publicSeedQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.Interval.PRFDerived.Query.publicSeed :
        GXMSS.Interval.PRFDerived.Query PP M h v))

/-- One start response consumes one PRF-function query. -/
private theorem startQuery_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    IsTotalQueryBound (startQuery (M := M) projection pp epoch chain) 1 := by
  unfold startQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.Interval.PRFDerived.Query.start pp epoch chain :
        GXMSS.Interval.PRFDerived.Query PP M h v))

/-- Exactly the active start enumeration is charged. -/
private theorem startQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (startQueries (M := M) (v := v) I p pp)
    ((I.last.val - I.first.val + 1) * v) := by
  unfold startQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using query_bound_fin_mOfFn _
    (fun i => startQuery_bound p pp
    (GXMSS.Interval.PRFDerived.activeEpoch I i.divNat) i.modNat)

/-- Setup makes one function call for every maximal inactive frontier node. -/
theorem fillerQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (fillerQueries (M := M) (v := v) I p pp)
      (Fintype.card (Subtree.FrontierNode I)) := by
  unfold fillerQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using query_bound_fin_mOfFn
    (fun i => fillerQuery (M := M) (v := v) p pp
      ((Fintype.equivFin (Subtree.FrontierNode I)).symm i))
    (fun i => (isQueryBound_map_iff _ _ _ _ _).mpr
      (functionQuery_bound (S := Response)
        (GXMSS.Interval.PRFDerived.Query.filler pp
          ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.1
          ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.2)))

private theorem startQueries_real (prf : SharedPRF Key PP M Response h v)
    (I : Interval h) (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (key : Key) (pp : PP) :
    simulateQ (prf.prfRealQueryImpl key) (startQueries I p pp) =
      pure (GXMSS.Interval.PRFDerived.starts I prf.eval p key pp) := by
  unfold startQueries
  rw [simulateQ_map]
  rw [simulateQ_fin_mOfFn_pure
    (g := fun index => p.chainStart (prf.eval key
      (.start pp (GXMSS.Interval.PRFDerived.activeEpoch I index.divNat) index.modNat)))
    (hfg := fun index => by simp [startQuery])]
  simp only [map_pure]
  congr 1
  unfold GXMSS.Interval.PRFDerived.starts
  congr 1
  funext i chain
  have hi := (finProdFinEquiv (m := I.last.val - I.first.val + 1) (n := v)).symm_apply_apply
    (i, chain)
  exact congrArg (fun ij => p.chainStart (prf.eval key
    (.start pp (GXMSS.Interval.PRFDerived.activeEpoch I ij.1) ij.2))) hi

private theorem fillerQueries_real (prf : SharedPRF Key PP M Response h v)
    (I : Interval h) (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (key : Key) (pp : PP) :
    simulateQ (prf.prfRealQueryImpl key) (fillerQueries I p pp) =
      pure (GXMSS.Interval.PRFDerived.fillers I prf.eval p key pp) := by
  unfold fillerQueries
  rw [simulateQ_map]
  rw [simulateQ_fin_mOfFn_pure
    (g := fun i => p.fillerDigest (prf.eval key (.filler pp
      ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.1
      ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.2)))
    (hfg := fun i => by simp [fillerQuery])]
  simp only [map_pure]
  congr 1
  funext node
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Query the ordered retry coordinates and project every response to a randomizer. -/
@[expose] def retryQueries (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (List R) :=
  (Fin.mOfFn budget fun attempt =>
    projection.retryRandomizer <$>
      PRFScheme.functionQuery (.retry pp epoch message attempt.val)).map List.ofFn

/-- Every reached retry input consumes one function-oracle call. -/
private theorem retryQueries_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (retryQueries (v := v) projection budget pp epoch message) budget := by
  unfold retryQueries
  change IsTotalQueryBound
    (List.ofFn <$> Fin.mOfFn budget (fun attempt => projection.retryRandomizer <$>
      PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val)))
    budget
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using
    (query_bound_fin_mOfFn
      (fun attempt : Fin budget => projection.retryRandomizer <$>
        PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val))
      (fun attempt => (isQueryBound_map_iff _ _ _ _ _).mpr
        (functionQuery_bound (S := Response)
          (GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val))))

/-- Independent projected responses for one eligible signing call's finite retry budget. -/
private def projectedRetries [SampleableType Response]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) : ProbComp (List R) :=
  List.ofFn <$> Fin.mOfFn budget (fun _ => projection.retryRandomizer <$> ($ᵗ Response))

/-- One projected response has exactly the canonical uniform retry-randomizer law. -/
@[expose] def RetrySamplingLaw [SampleableType Response] [SampleableType R]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace R := ⊤
  𝒟[projection.retryRandomizer <$> ($ᵗ Response)] = 𝒟[$ᵗ R]

/-- Seed, active starts and frontier roots, kept together for the complete interaction. -/
private noncomputable def keyMaterialQueries (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (PP × (Fin (2 ^ h) → Fin v → H) × Fillers I H) := do
  let pp ← publicSeedQuery p
  let starts ← startQueries I p pp
  let fillers ← fillerQueries I p pp
  pure (pp, starts, fillers)

private theorem keyMaterialQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (keyMaterialQueries (M := M) (h := h) (v := v) I p)
      (1 + (I.last.val - I.first.val + 1) * v + Fintype.card (Subtree.FrontierNode I)) := by
  unfold keyMaterialQueries
  rw [Nat.add_assoc]
  apply isTotalQueryBound_bind (publicSeedQuery_bound p)
  intro pp
  apply isTotalQueryBound_bind (startQueries_bound I p pp)
  intro starts
  simpa only [Nat.add_zero] using isTotalQueryBound_bind (fillerQueries_bound I p pp)
    (fun fillers => (show IsTotalQueryBound (pure (pp, starts, fillers) : OracleComp
      (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response) _) 0
      from trivial))

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
  let alg := oracleScheme hash enc projection budget I
  let forward : QueryImpl unifSpec
      (OracleComp (PRFScheme.PRFOracleSpec
        (GXMSS.Interval.PRFDerived.Query PP M h v) Response)) :=
    fun q => liftM (OracleSpec.query (Sum.inl q) :
      OracleQuery (PRFScheme.PRFOracleSpec
        (GXMSS.Interval.PRFDerived.Query PP M h v) Response) _)
  forward.liftTarget (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v))
        (OracleComp (PRFScheme.PRFOracleSpec
          (GXMSS.Interval.PRFDerived.Query PP M h v) Response))) +
      SyncSignatureUnforgeability.signingOracle alg core

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
  exact GXMSS.PRFDerived.SigningSimulation.signingHandler_query_bound
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

/-- The real evaluator supplies the exact indexed retry list. -/
private theorem retryQueries_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (key : Key) (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (retryQueries projection budget pp epoch message) =
    pure (GXMSS.Interval.PRFDerived.retryRandomizers budget prf.eval
      projection
      key pp epoch message) := by
  unfold retryQueries
  change simulateQ (prf.prfRealQueryImpl key)
    (List.ofFn <$> Fin.mOfFn budget (fun attempt => projection.retryRandomizer <$>
      PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val))) = _
  rw [simulateQ_map]
  have hflat : simulateQ (prf.prfRealQueryImpl key)
      (Fin.mOfFn budget fun attempt => projection.retryRandomizer <$>
        PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val)) =
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
      GXMSS.PRFDerived.SignResult.output]

/-- The source scheme with its sampled evaluator key fixed for one interaction. -/
private def fixedKeyScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
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
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h) (key : Key) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle
      (fixedKeyScheme hash enc prf projection budget I key) key

/-- Per-query real simulation preserves the synchronized history, including failed
answers and already consumed epochs. -/
private theorem adaptiveHandler_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
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
          simp only [adaptiveHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
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
    (prf : SharedPRF Key PP M Response h v)
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
  erw [hcomp]
  unfold SyncSignatureUnforgeability.interaction fixedKeyScheme fixedKeyHandler
  simp only [pure_bind]
  erw [map_eq_bind_pure_comp]
  rfl

/-- The real PRF distinguisher observes the complete strong synchronized game.
The same runtime interpretation therefore preserves missing mass as well as returned failure. -/
theorem randgenPRFReduction_real_strong [SampleableType Key] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (keyLaw : prf.UniformKey) :
    prf.prfRealExperiment (randgenPRFReduction hash enc projection budget I adv) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval projection budget I) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval projection budget I) adv := by
  unfold PRFScheme.prfRealExperiment randgenPRFReduction
  rw [keyLaw]
  change (do
    let key ← $ᵗ Key
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
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc projection budget I adv)
      (fun query => query.isRight = true)
      (1 + (I.last.val - I.first.val + 1) * v +
        Fintype.card (Subtree.FrontierNode I) + qs * budget) := by
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
    apply isQueryBoundP_simulateQ_run_weighted
      (p := fun query => query.isRight = true)
      (q := fun query => query.isRight = true)
      (adaptiveHandler hash enc projection budget I pair.2)
      budget
    · intro query hp history
      change query.isRight = true at hp
      simpa only [hp, ite_true] using
        adaptiveHandler_query_bound hash enc projection budget I pair.2 query history
    · intro query hp history
      change ¬ query.isRight = true at hp
      simpa only [ite_eq_right hp] using
        adaptiveHandler_query_bound hash enc projection budget I pair.2 query history
    · exact hbound pair.1
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

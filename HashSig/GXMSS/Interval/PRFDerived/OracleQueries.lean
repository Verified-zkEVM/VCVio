/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerivedScheme
public import HashSig.GXMSS.Interval.FrontierCount
public import HashSig.GXMSS.PRFDerived.SamplingLaws
public import VCVio.CryptoFoundations.PRF.ProjectedQueries

/-!
# Interval PRF setup and retry queries

Typed coordinates enumerate the seed, active starts, inactive frontier and eager retries. Query
counts include every prefetched retry; the real handler retains the actual evaluator's values.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding ENNReal GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory PRFScheme.QuerySimulation PRFScheme.ProjectedQueries
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Setup queries one seed, each active chain start and each inactive frontier root. -/
@[expose] def keyMaterialQueryCount (I : Interval h) (v : ℕ) : ℕ :=
  1 + I.length * v + Fintype.card (Subtree.FrontierNode I)

/-- All-request accounting adds the full eager retry budget for each signing request. -/
@[expose] def functionQueryCount (I : Interval h) (v qs K : ℕ) : ℕ :=
  keyMaterialQueryCount I v + qs * K

/-- The distinguished response has exactly the THF public-seed sampling law. -/
@[expose] def PublicSeedSamplingLaw [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  GXMSS.PRFDerived.Unforgeability.PublicSeedSamplingLaw hash projection.toComplete

/-- Each distinct chain-start response projects to the canonical uniform start law. -/
@[expose] def ChainStartSamplingLaw [SampleableType Response] [SampleableType H]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  GXMSS.PRFDerived.Unforgeability.ChainStartSamplingLaw projection.toComplete

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

/-- The public-seed coordinate incurs one function-oracle call. -/
theorem publicSeedQuery_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (publicSeedQuery (M := M) (h := h) (v := v) projection) 1 := by
  unfold publicSeedQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.Interval.PRFDerived.Query.publicSeed :
        GXMSS.Interval.PRFDerived.Query PP M h v))

/-- One start response consumes one PRF-function query. -/
theorem startQuery_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    IsTotalQueryBound (startQuery (M := M) projection pp epoch chain) 1 := by
  unfold startQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.Interval.PRFDerived.Query.start pp epoch chain :
        GXMSS.Interval.PRFDerived.Query PP M h v))

/-- Exactly the active start enumeration is charged. -/
theorem startQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (startQueries (M := M) (v := v) I p pp)
    ((I.last.val - I.first.val + 1) * v) := by
  unfold startQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using OracleComp.isTotalQueryBound_fin_mOfFn _
    (fun i => startQuery_bound p pp
    (GXMSS.Interval.PRFDerived.activeEpoch I i.divNat) i.modNat)

/-- Setup makes one function call for every maximal inactive frontier node. -/
theorem fillerQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (fillerQueries (M := M) (v := v) I p pp)
      (Fintype.card (Subtree.FrontierNode I)) := by
  unfold fillerQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using OracleComp.isTotalQueryBound_fin_mOfFn
    (fun i => fillerQuery (M := M) (v := v) p pp
      ((Fintype.equivFin (Subtree.FrontierNode I)).symm i))
    (fun i => (isQueryBound_map_iff _ _ _ _ _).mpr
      (functionQuery_bound (S := Response)
        (GXMSS.Interval.PRFDerived.Query.filler pp
          ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.1
          ((Fintype.equivFin (Subtree.FrontierNode I)).symm i).val.2)))

theorem startQueries_real
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
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

theorem fillerQueries_real
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
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
  responseQueries projection.retryRandomizer budget
    (fun attempt => GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val)

/-- Every reached retry input consumes one function-oracle call. -/
theorem retryQueries_bound
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (retryQueries (v := v) projection budget pp epoch message) budget := by
  exact responseQueries_bound projection.retryRandomizer budget
    (fun attempt => GXMSS.Interval.PRFDerived.Query.retry pp epoch message attempt.val)

/-- Independent projected responses for one eligible signing call's finite retry budget. -/
@[expose] def projectedRetries [SampleableType Response]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) : ProbComp (List R) :=
  List.ofFn <$> Fin.mOfFn budget (fun _ => projection.retryRandomizer <$> ($ᵗ Response))

/-- One projected response has exactly the canonical uniform retry-randomizer law. -/
@[expose] def RetrySamplingLaw [SampleableType Response] [SampleableType R]
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  GXMSS.PRFDerived.Unforgeability.RetrySamplingLaw projection.toComplete

/-- Seed, active starts and frontier roots, kept together for the complete interaction. -/
@[expose] noncomputable def keyMaterialQueries (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
      (PP × (Fin (2 ^ h) → Fin v → H) × Fillers I H) := do
  let pp ← publicSeedQuery p
  let starts ← startQueries I p pp
  let fillers ← fillerQueries I p pp
  pure (pp, starts, fillers)

/-- The setup program charges its seed, active starts and complete frontier. -/
theorem keyMaterialQueries_bound (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (keyMaterialQueries (M := M) (h := h) (v := v) I p)
      (keyMaterialQueryCount I v) := by
  unfold keyMaterialQueryCount Interval.length
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

/-- The real evaluator supplies the exact indexed retry list. -/
theorem retryQueries_real
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (key : Key) (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (retryQueries projection budget pp epoch message) =
    pure (GXMSS.Interval.PRFDerived.retryRandomizers budget prf.eval
      projection
      key pp epoch message) := by
  unfold retryQueries
  rw [responseQueries_real]
  rfl


end GXMSS.Interval.PRFDerived.Unforgeability

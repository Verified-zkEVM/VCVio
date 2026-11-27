/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction
-- The material-normalization equality is private to the native interaction implementation.
import all HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction

/-!
# Interval PRF ideal interaction

One persistent complete-response cache supplies independent projections at fresh typed inputs.
Adaptive signing preserves the unused-epoch cache invariant and the complete first-request history.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding ENNReal GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory
open OracleComp.ProgramLogic.Relational
open PRFScheme.QuerySimulation PRFScheme.ProjectedQueries
open SyncSignatureUnforgeability.PRFSimulation
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The filler projection law is required at each frontier coordinate actually queried. -/
@[expose] def UsedFillerSamplingLaw [SampleableType Response] [SampleableType H]
    (I : Interval h) (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : Prop :=
  ∀ _ : Subtree.FrontierNode I, FillerSamplingLaw p

/-- Full range has no queried filler coordinate and imposes no filler projection law. -/
theorem usedFillerSamplingLaw_full [SampleableType Response] [SampleableType H]
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    UsedFillerSamplingLaw (Interval.full h) p := by
  intro node
  exact isEmptyElim node

private theorem evalDistEq_of_eq {A : Type} {x y : ProbComp A} (h : x = y) : x =ᵈ y := by
  subst y
  exact EvalDistEq.rfl

/-- The named whole-interaction idealization property. The observation retains public
key, forgery and synchronized history, and therefore retains failures and missing mass. -/
@[expose] def IdealInteractionCorrespondence [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : Prop :=
  letI : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
    (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
    (adaptiveInteraction hash enc p K I adv)).run' ∅] =
    𝒟[SyncSignatureUnforgeability.interaction (GXMSS.Interval.scheme hash enc K I) adv]

/-- Uniform complete starts restrict to independent uniform active rows. Unused inactive draws
are integrated out; no deterministic extension is equated with the full secret array. -/
theorem active_starts_sampling [SampleableType H] (I : Interval h) :
    let : MeasurableSpace H := ⊤
    𝒟[GXMSS.Interval.PRFDerived.restrictStarts I <$> GXMSS.sampleStarts H h v] =
      𝒟[Fin.mOfFn (I.last.val - I.first.val + 1)
        (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))] := by
  dsimp only
  let : MeasurableSpace H := ⊤
  let row : ProbComp (Fin v → H) := Fin.mOfFn v (fun _ => ($ᵗ H))
  have hr : 𝒟[row] = ProbabilityTheory.uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform v ($ᵗ H) SampleableType.evalDist_uniformSample
  have hs : 𝒟[Fin.mOfFn (I.last.val - I.first.val + 1) (fun _ => row)] =
      ProbabilityTheory.uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform _ row hr
  have hl : 𝒟[GXMSS.sampleStarts H h v] = ProbabilityTheory.uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform (2 ^ h) row hr
  rw [evalDist_map_of_discrete, hl, hs]
  exact ProbabilityTheory.uniformOn_univ_map_comp_injective
    (GXMSS.Interval.PRFDerived.activeEpoch_injective I)

private def flatToMatrix {H : Type} (m n : ℕ) :
    (Fin (m * n) → H) ≃ (Fin m → Fin n → H) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl H)).trans
    (Equiv.curry (Fin m) (Fin n) H)

private def projectedActiveStarts [SampleableType Response] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    ProbComp (Fin (2 ^ h) → Fin v → H) :=
  (fun flat => GXMSS.Interval.PRFDerived.extendStarts I
    (flatToMatrix (I.last.val - I.first.val + 1) v flat)) <$>
      Fin.mOfFn ((I.last.val - I.first.val + 1) * v)
        (fun _ => p.chainStart <$> ($ᵗ Response))

private noncomputable def projectedFillers [SampleableType Response] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) : ProbComp (Fillers I H) :=
  (fun flat node => flat (Fintype.equivFin (Subtree.FrontierNode I) node)) <$>
    Fin.mOfFn (Fintype.card (Subtree.FrontierNode I))
      (fun _ => p.fillerDigest <$> ($ᵗ Response))

private theorem startInput_injective (I : Interval h) (pp : PP) : Function.Injective
    (fun i : Fin ((I.last.val - I.first.val + 1) * v) =>
      (GXMSS.Interval.PRFDerived.Query.start pp
        (GXMSS.Interval.PRFDerived.activeEpoch I i.divNat) i.modNat :
          GXMSS.Interval.PRFDerived.Query PP M h v)) := by
  intro i j hij
  obtain ⟨_, hepoch, hchain⟩ := GXMSS.PRFDerived.Query.start.inj
      (GXMSS.Interval.PRFDerived.Query.complete.inj hij)
  have hi := GXMSS.Interval.PRFDerived.activeEpoch_injective I hepoch
  exact (finProdFinEquiv (m := I.last.val - I.first.val + 1) (n := v)).symm.injective
    (Prod.ext hi hchain)

private theorem fillerInput_injective (I : Interval h) (pp : PP) : Function.Injective
    (fun i : Fin (Fintype.card (Subtree.FrontierNode I)) =>
      let node := (Fintype.equivFin (Subtree.FrontierNode I)).symm i
      let (level, index) := node.val
      (GXMSS.Interval.PRFDerived.Query.filler pp level index :
        GXMSS.Interval.PRFDerived.Query PP M h v)) := by
  intro i j hij
  obtain ⟨_, hlevel, hindex⟩ := GXMSS.Interval.PRFDerived.Query.filler.inj hij
  apply (Fintype.equivFin (Subtree.FrontierNode I)).symm.injective
  exact Subtype.ext (Prod.ext hlevel hindex)

private theorem startQueries_ideal_fresh [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : ∀ i : Fin ((I.last.val - I.first.val + 1) * v),
      cache (.start pp (GXMSS.Interval.PRFDerived.activeEpoch I i.divNat) i.modNat) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (startQueries I p pp)).run' cache = projectedActiveStarts I p := by
  unfold startQueries projectedActiveStarts
  simp only [startQuery, ← Fin.mOfFn_map]
  rw [simulateQ_map, simulateQ_map, state_run'_map, state_run'_map]
  rw [ideal_fin_queries_fresh _ _ (startInput_injective I pp) cache hfresh]
  rfl

private theorem fillerQueries_ideal_fresh [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : ∀ i : Fin (Fintype.card (Subtree.FrontierNode I)),
      let node := (Fintype.equivFin (Subtree.FrontierNode I)).symm i
      let address := node.val
      cache (.filler pp address.1 address.2) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (fillerQueries I p pp)).run' cache = projectedFillers I p := by
  unfold fillerQueries projectedFillers
  simp only [fillerQuery, ← Fin.mOfFn_map]
  rw [simulateQ_map, simulateQ_map, state_run'_map, state_run'_map]
  rw [ideal_fin_queries_fresh _ _ (fillerInput_injective I pp) cache hfresh]

private theorem startQueries_avoids_filler (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp seed : PP)
    (level : Fin (h + 1)) (index : Fin (2 ^ h)) :
    AllQueriesSatisfy (startQueries (M := M) (v := v) I p pp)
      (fun query => ∀ d, query = Sum.inr d →
        d ≠ GXMSS.Interval.PRFDerived.Query.filler seed level index) := by
  unfold startQueries
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply allQueriesSatisfy_fin_mOfFn
  intro i
  unfold startQuery
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  intro heq
  cases heq

private theorem projectedActiveStarts_sampling [SampleableType H] [SampleableType Response]
    (I : Interval h) (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (hstart : ChainStartSamplingLaw p) :
    letI : MeasurableSpace H := ⊤
    𝒟[projectedActiveStarts (v := v) I p] =
      𝒟[GXMSS.Interval.PRFDerived.extendStarts I <$>
        Fin.mOfFn (I.last.val - I.first.val + 1)
          (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))] := by
  let : MeasurableSpace H := ⊤
  have hbase : 𝒟[p.chainStart <$> ($ᵗ Response)] = uniformOn Set.univ :=
    hstart.trans SampleableType.evalDist_uniformSample
  have hflat : 𝒟[Fin.mOfFn ((I.last.val - I.first.val + 1) * v)
      (fun _ => p.chainStart <$> ($ᵗ Response))] = uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform _ _ hbase
  have hinner : 𝒟[Fin.mOfFn v (fun _ => ($ᵗ H))] = uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform v ($ᵗ H) SampleableType.evalDist_uniformSample
  have hnested : 𝒟[Fin.mOfFn (I.last.val - I.first.val + 1)
      (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))] = uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform _ _ hinner
  unfold projectedActiveStarts
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, hnested]
  have hmatrix : (uniformOn Set.univ : Measure (Fin ((I.last.val - I.first.val + 1) * v) → H)).map
      (flatToMatrix (I.last.val - I.first.val + 1) v) = uniformOn Set.univ :=
    map_uniformOn_univ_of_bijective Measurable.of_discrete
      (flatToMatrix (I.last.val - I.first.val + 1) v).bijective
  rw [hflat]
  rw [← hmatrix, Measure.map_map (Measurable.of_discrete) (Measurable.of_discrete)]
  rfl

private theorem sampleFillers_eq_mPi [SampleableType H] (I : Interval h) :
    sampleFillers I H = Fintype.mPi (fun _ : Subtree.FrontierNode I => ($ᵗ H)) := by
  unfold sampleFillers
  split
  · rename_i hc
    let : IsEmpty (Subtree.FrontierNode I) := Fintype.card_eq_zero_iff.mp hc
    let dummy : H := Classical.choice (inferInstance : Nonempty H)
    have seqzero (n : ℕ) (hn : n = 0) :
        Fin.mOfFn n (fun _ => ($ᵗ H)) = pure (fun _ : Fin n => dummy) := by
      subst n
      simp only [Fin.mOfFn]
      congr 1
      funext i
      exact i.elim0
    unfold Fintype.mPi
    rw [seqzero _ hc, map_pure]
    congr 1
    funext node
    exact isEmptyElim node
  · rfl

private theorem projectedFillers_sampling [SampleableType H] [SampleableType Response]
    (I : Interval h) (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (hfiller : UsedFillerSamplingLaw I p) :
    letI : MeasurableSpace H := ⊤
    𝒟[projectedFillers I p] = 𝒟[sampleFillers I H] := by
  let : MeasurableSpace H := ⊤
  by_cases hfront : Nonempty (Subtree.FrontierNode I)
  · have hbase : 𝒟[p.fillerDigest <$> ($ᵗ Response)] = uniformOn Set.univ :=
      (hfiller (Classical.choice hfront)).trans SampleableType.evalDist_uniformSample
    have hflat : 𝒟[Fin.mOfFn (Fintype.card (Subtree.FrontierNode I))
        (fun _ => p.fillerDigest <$> ($ᵗ Response))] = uniformOn Set.univ :=
      evalDist_mOfFn_const_uniform _ _ hbase
    unfold projectedFillers
    rw [sampleFillers_eq_mPi I, evalDist_map_of_discrete, hflat,
      evalDist_mPi_const_uniform ($ᵗ H) SampleableType.evalDist_uniformSample]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete
      (Equiv.arrowCongr (Fintype.equivFin (Subtree.FrontierNode I)).symm (Equiv.refl H)).bijective
  · let : IsEmpty (Subtree.FrontierNode I) := ⟨fun node => hfront ⟨node⟩⟩
    have hc : Fintype.card (Subtree.FrontierNode I) = 0 := Fintype.card_eq_zero
    have hprogram : projectedFillers I p = sampleFillers I H := by
      have hseq (n : ℕ) (hn : n = 0) :
          Fin.mOfFn n (fun _ => p.fillerDigest <$> ($ᵗ Response)) =
            pure (fun i : Fin n => False.elim (by have := i.isLt; omega)) := by
        subst n
        rfl
      unfold projectedFillers
      rw [hseq _ hc, map_pure]
      unfold sampleFillers
      rw [dite_eq_left hc]
    exact congrArg (fun program : ProbComp (Fillers I H) => 𝒟[program]) hprogram

private theorem keyMaterial_ideal_projected [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries I p)).run' ∅ = (do
        let response ← $ᵗ Response
        let starts ← projectedActiveStarts I p
        let fillers ← projectedFillers I p
        pure (p.publicParameter response, starts, fillers)) := by
  unfold keyMaterialQueries
  rw [simulateQ_bind, StateT.run'_bind']
  simp only [publicSeedQuery, simulateQ_map,
    PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery, StateT.run_map]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply, pure_bind]
  apply bind_congr
  intro response
  let pp := p.publicParameter response
  let seedCache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache :=
    (∅ : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
      .publicSeed response
  have hstarts : ∀ i : Fin ((I.last.val - I.first.val + 1) * v),
      seedCache (.start pp (GXMSS.Interval.PRFDerived.activeEpoch I i.divNat) i.modNat) = none := by
    intro i
    rw [QueryCache.cacheQuery_of_ne]
    · exact QueryCache.empty_apply _
    · intro hcontra
      cases hcontra
  have hfillers (result : (Fin (2 ^ h) → Fin v → H) ×
      ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
      (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
        (startQueries I p pp)).run seedCache)) :
      ∀ i : Fin (Fintype.card (Subtree.FrontierNode I)),
        let node := (Fintype.equivFin (Subtree.FrontierNode I)).symm i
        let address := node.val
        result.2 (.filler pp address.1 address.2) = none := by
    intro i
    let node := (Fintype.equivFin (Subtree.FrontierNode I)).symm i
    let address := node.val
    dsimp only
    rw [ideal_cache_frame (.filler pp address.1 address.2) _
      (startQueries_avoids_filler I p pp pp address.1 address.2) seedCache result hresult]
    rw [QueryCache.cacheQuery_of_ne]
    · exact QueryCache.empty_apply _
    · intro hcontra
      cases hcontra
  rw [simulateQ_bind, StateT.run'_bind']
  calc
    _ = (do
      let result ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
        (startQueries I p pp)).run seedCache
      let fillers ← projectedFillers I p
      pure (pp, result.1, fillers)) := by
        apply bind_congr_of_forall_mem_support
        intro result hresult
        rcases result with ⟨active, table⟩
        dsimp only
        rw [simulateQ_bind, StateT.run'_bind']
        simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
        calc
          _ = (fun fillers => (pp, active, fillers)) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl
                (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
                (fillerQueries I p pp)).run' table := by
                simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, pp]
          _ = _ := by
            rw [fillerQueries_ideal_fresh I p pp table (hfillers (active, table) hresult)]
            rw [map_eq_bind_pure_comp]
            rfl
    _ = (do
      let starts ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
        (startQueries I p pp)).run' seedCache
      let fillers ← projectedFillers I p
      pure (pp, starts, fillers)) := by
        simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by rw [startQueries_ideal_fresh I p pp seedCache hstarts]

private theorem keyMaterial_ideal_sampling [SampleableType H] [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v) (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hfiller : UsedFillerSamplingLaw I p) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries I p)).run' ∅ =ᵈ (do
        let pp ← hash.thf.seedGen
        let active ← Fin.mOfFn (I.last.val - I.first.val + 1)
          (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))
        let fillers ← sampleFillers I H
        pure (pp, GXMSS.Interval.PRFDerived.extendStarts I active, fillers)) := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  have hseed' : p.publicParameter <$> ($ᵗ Response) =ᵈ hash.thf.seedGen :=
    EvalDistEq.of_evalDist_eq hseed
  have hstarts' := EvalDistEq.of_evalDist_eq (projectedActiveStarts_sampling (v := v) I p hstart)
  have hfillers' := EvalDistEq.of_evalDist_eq (projectedFillers_sampling I p hfiller)
  rw [keyMaterial_ideal_projected I p]
  have hnormalize : (do
      let response ← $ᵗ Response
      let starts ← projectedActiveStarts (v := v) I p
      let fillers ← projectedFillers I p
      pure (p.publicParameter response, starts, fillers)) = (do
        let pp ← p.publicParameter <$> ($ᵗ Response)
        let starts ← projectedActiveStarts (v := v) I p
        let fillers ← projectedFillers I p
        pure (pp, starts, fillers)) := by simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hnormalize]
  apply hseed'.bind
  intro pp
  have heq := hstarts'.bind (fun starts => hfillers'.bind
    (fun fillers => EvalDistEq.rfl (mx := pure (pp, starts, fillers))))
  simpa [map_eq_bind_pure_comp, bind_assoc] using heq

/-- Every retry coordinate of an unused epoch remains absent from the full-response cache. -/
private def RetryFresh (pp : PP)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v))
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) : Prop :=
  ∀ ep, history ep = none → ∀ msg attempt, cache (.retry pp ep msg attempt) = none

private theorem allQueries_map {ι A B : Type} {spec : OracleSpec ι}
    (program : OracleComp spec A) (f : A → B) (pred : ι → Prop)
    (hprogram : AllQueriesSatisfy program pred) : AllQueriesSatisfy (f <$> program) pred := by
  rw [allQueriesSatisfy_def] at hprogram ⊢
  exact (isQueryBound_map_iff _ _ _ _ _).mpr hprogram

private theorem functionQuery_avoids {D S : Type} (input target : D) (hne : input ≠ target) :
    AllQueriesSatisfy (PRFScheme.functionQuery (R := S) input)
      (fun query => ∀ d, query = Sum.inr d → d ≠ target) := by
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  exact hne

private theorem keyMaterial_avoids_retry (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (seed : PP) (ep : Fin (2 ^ h)) (msg : M) (attempt : ℕ) :
    AllQueriesSatisfy (keyMaterialQueries (h := h) (v := v) I p)
      (fun query => ∀ d, query = Sum.inr d →
        d ≠ GXMSS.Interval.PRFDerived.Query.retry seed ep msg attempt) := by
  unfold keyMaterialQueries publicSeedQuery
  apply allQueriesSatisfy_bind
  · apply allQueries_map
    exact functionQuery_avoids _ _ (by intro heq; cases heq)
  · intro pp
    apply allQueriesSatisfy_bind
    · unfold startQueries
      apply allQueries_map
      apply allQueriesSatisfy_fin_mOfFn
      intro i
      unfold startQuery
      apply allQueries_map
      exact functionQuery_avoids _ _ (by intro heq; cases heq)
    · intro starts
      apply allQueriesSatisfy_bind
      · unfold fillerQueries
        apply allQueries_map
        apply allQueriesSatisfy_fin_mOfFn
        intro i
        unfold fillerQuery
        apply allQueries_map
        exact functionQuery_avoids _ _ (by intro heq; cases heq)
      · intro fillers
        exact allQueriesSatisfy_pure _ _

private theorem keyMaterial_ideal_cache [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] (I : Interval h)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (result : (PP × (Fin (2 ^ h) → Fin v → H) × Fillers I H) ×
      ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries I p)).run ∅)) :
    let material := result.1
    RetryFresh (H := H) (R := R) material.1
      SyncSignatureUnforgeability.emptyHistory result.2 := by
  let material := result.1
  dsimp only
  intro ep _ msg attempt
  rw [ideal_cache_frame _ _ (keyMaterial_avoids_retry I p material.1 ep msg attempt)
    ∅ result hresult]
  exact QueryCache.empty_apply _

private theorem retryInput_injective (pp : PP) (ep : Fin (2 ^ h)) (msg : M) (K : ℕ) :
    Function.Injective (fun i : Fin K =>
      (GXMSS.Interval.PRFDerived.Query.retry pp ep msg i.val :
        GXMSS.Interval.PRFDerived.Query PP M h v)) := by
  intro i j hij
  obtain ⟨_, _, _, hattempt⟩ := GXMSS.PRFDerived.Query.retry.inj
      (GXMSS.Interval.PRFDerived.Query.complete.inj hij)
  exact Fin.ext hattempt

/-- Active first-success signing has the direct recursive retry law for an arbitrary fixed key. -/
private theorem retry_sampling_sign [SampleableType Response] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (hretry : RetrySamplingLaw p) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) (ep : Fin (2 ^ h)) (msg : M)
    (he : Epoch.IsActive I ep) :
    letI : MeasurableSpace (Option (Signature R H h v)) := ⊤
    𝒟[(fun randomizers =>
      (GXMSS.Interval.PRFDerived.signResult hash enc I sk ep msg randomizers).output) <$>
      projectedRetries p K] = 𝒟[GXMSS.Interval.sign hash enc K I sk ep msg] := by
  let complete := sk.complete
  apply eager_retry_sampling p.retryRandomizer hretry
    (fun randomizers =>
      (GXMSS.Interval.PRFDerived.signResult hash enc I sk ep msg randomizers).output)
    (fun r => (enc.value complete.seed msg r ep).map
      (fun word => GXMSS.Interval.signatureOfWord hash I sk ep (word, r)))
    (fun n => GXMSS.Interval.sign hash enc n I sk ep msg) ?_ ?_ ?_ ?_ K
  · rfl
  · intro r rs
    unfold GXMSS.Interval.PRFDerived.signResult
    dsimp only
    rw [GXMSS.PRFDerived.signResult_cons]
    cases hv : enc.value complete.seed msg r ep with
    | some word => rfl
    | none =>
        cases GXMSS.PRFDerived.signResult hash enc sk.complete ep msg rs <;> rfl
  · simp [GXMSS.Interval.sign, he, IncomparableEncoding.retry]
  · intro n
    simp only [GXMSS.Interval.sign, ite_eq_left he, IncomparableEncoding.retry_succ, map_bind]
    apply bind_congr
    intro r
    cases enc.value complete.seed msg r ep <;> rfl

private theorem oracleSign_ideal_output [SampleableType Response] [SampleableType R]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (hretry : RetrySamplingLaw p) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) (ep : Fin (2 ^ h)) (msg : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v))
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : let complete := sk.complete; RetryFresh complete.seed history cache)
    (hunused : history ep = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc p K I sk ep msg)).run' cache =ᵈ
      GXMSS.Interval.sign hash enc K I sk ep msg := by
  let complete := sk.complete
  by_cases he : Epoch.IsActive I ep
  · unfold oracleSign
    rw [ite_eq_left he, simulateQ_bind, StateT.run'_bind']
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure, bind_pure_comp]
    have heager := responseQueries_ideal_fresh p.retryRandomizer K
      (fun i => GXMSS.Interval.PRFDerived.Query.retry complete.seed ep msg i.val)
      (retryInput_injective complete.seed ep msg K) cache
      (fun i => hfresh ep hunused msg i.val)
    have hnormalize :
        ((fun result =>
          (GXMSS.Interval.PRFDerived.signResult hash enc I sk ep msg result.1).output) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl
            (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
            (retryQueries p K complete.seed ep msg)).run cache) =
        (fun randomizers =>
          (GXMSS.Interval.PRFDerived.signResult hash enc I sk ep msg randomizers).output) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl
            (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
            (retryQueries p K complete.seed ep msg)).run' cache := by
      simp [StateT.run'_eq, Functor.map_map]
    rw [hnormalize]
    change (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (retryQueries p K complete.seed ep msg)).run' cache = _ at heager
    rw [heager]
    let : MeasurableSpace (Option (Signature R H h v)) := ⊤
    exact EvalDistEq.of_evalDist_eq (retry_sampling_sign hash enc p K hretry I sk ep msg he)
  · simp [oracleSign, he, GXMSS.Interval.sign]

private theorem oracleSign_ideal_preserves [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) (ep : Fin (2 ^ h)) (msg : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v))
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : let complete := sk.complete; RetryFresh complete.seed history cache)
    (result : Option (Signature R H h v) ×
      ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc p K I sk ep msg)).run cache)) :
    let complete := sk.complete
    RetryFresh complete.seed (Function.update history ep (some (msg, result.1))) result.2 := by
  let complete := sk.complete
  dsimp only
  intro other hunused message attempt
  have hne : other ≠ ep := by
    intro heq
    subst other
    simp [Function.update] at hunused
  have htarget : ∀ i : Fin K,
      (GXMSS.Interval.PRFDerived.Query.retry complete.seed ep msg i.val :
        GXMSS.Interval.PRFDerived.Query PP M h v) ≠
        .retry complete.seed other message attempt := by
    intro i heq
    obtain ⟨_, hepoch, _, _⟩ := GXMSS.PRFDerived.Query.retry.inj
      (GXMSS.Interval.PRFDerived.Query.complete.inj heq)
    exact hne hepoch.symm
  have havoid : AllQueriesSatisfy (oracleSign hash enc p K I sk ep msg)
      (fun query => ∀ d, query = Sum.inr d →
        d ≠ GXMSS.Interval.PRFDerived.Query.retry complete.seed other message attempt) := by
    unfold oracleSign
    split
    · apply allQueriesSatisfy_bind
        (responseQueries_avoids p.retryRandomizer K
          (fun i => GXMSS.Interval.PRFDerived.Query.retry complete.seed ep msg i.val)
          _ htarget)
      intro randomizers
      exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _
  rw [ideal_cache_frame _ _ havoid cache result hresult]
  exact hfresh other (by simpa [Function.update, hne] using hunused) message attempt

/-- For any fixed interval material and fresh unused-epoch retries, the cached ideal interaction
has the same returned forgery and full synchronized history as direct independent retry sampling. -/
private theorem ideal_fixed_run_projected {A : Type}
    [SampleableType H] [SampleableType R] [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (hretry : RetrySamplingLaw p) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Fin (2 ^ h)) M (Signature R H h v)) A)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v))
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : let complete := sk.complete
      ∀ ep, history ep = none → ∀ msg attempt,
        cache (.retry complete.seed ep msg attempt) = none) :
    Prod.map id Prod.fst <$>
      (simulateQ (SyncSignatureUnforgeability.PRFSimulation.idealHandler
        (oracleScheme hash enc p K I) sk)
        program).run (history, cache) =ᵈ
      (simulateQ (SyncSignatureUnforgeability.PRFSimulation.fixedHandler
        (GXMSS.Interval.scheme hash enc K I) sk)
        program).run history := by
  let complete := sk.complete
  apply signingRun_projected (oracleScheme hash enc p K I) (GXMSS.Interval.scheme hash enc K I)
    sk sk (RetryFresh complete.seed) ?_ ?_ program history cache hfresh
  · intro ep msg hist table hf hunused
    exact oracleSign_ideal_output hash enc p K hretry I sk ep msg hist table hf hunused
  · intro ep msg hist table hf _ result hresult
    exact oracleSign_ideal_preserves hash enc p K I sk ep msg hist table hf result hresult

/-- Fixed-material adaptive ideal signing preserves the entire returned value and first-request
history, including failed and repeated requests. The initial freshness condition is explicit. -/
theorem ideal_fixed_interaction_correspondence {A : Type}
    [SampleableType H] [SampleableType R] [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (hretry : RetrySamplingLaw p) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Fin (2 ^ h)) M (Signature R H h v)) A)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v))
    (cache : ((GXMSS.Interval.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : let complete := sk.complete
      ∀ ep, history ep = none → ∀ msg attempt,
        cache (.retry complete.seed ep msg attempt) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      ((simulateQ (adaptiveHandler hash enc p K I sk) program).run history)).run' cache =ᵈ
      (simulateQ
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
            (Signature R H h v)) ProbComp) +
          SyncSignatureUnforgeability.signingOracle (GXMSS.Interval.scheme hash enc K I) sk)
        program).run history := by
  have hfixed := ideal_fixed_run_projected hash enc p K hretry I sk program history cache hfresh
  have hcompose := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
    (adaptiveHandler hash enc p K I sk) program history cache
  rw [StateT.run'_eq, hcompose]
  simp only [Functor.map_map]
  change Prod.map id Prod.fst <$>
    (simulateQ (idealHandler (oracleScheme hash enc p K I) sk) program).run
      (history, cache) =ᵈ (simulateQ (fixedHandler (GXMSS.Interval.scheme hash enc K I) sk)
        program).run history
  exact hfixed

private noncomputable def fixedMaterialInteraction [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (material : PP × (Fin (2 ^ h) → Fin v → H) × Fillers I H) :
    ProbComp (SyncSignatureUnforgeability.ExperimentResult
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :=
  let (pp, starts, fillers) := material
  let pair := GXMSS.Interval.keys hash I pp starts fillers
  (fun outcome => (pair.1, outcome.1, outcome.2)) <$>
    (simulateQ (fixedHandler (GXMSS.Interval.scheme hash enc K I) pair.2)
      (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory

private theorem directSign_eq_of_active_starts_eq [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ ep, Epoch.IsActive I ep → xs ep = ys ep)
    (ep : Fin (2 ^ h)) (msg : M) :
    GXMSS.Interval.sign hash enc K I (GXMSS.Interval.keys hash I pp xs fillers).2 ep msg =
      GXMSS.Interval.sign hash enc K I (GXMSS.Interval.keys hash I pp ys fillers).2 ep msg := by
  unfold GXMSS.Interval.sign
  by_cases he : Epoch.IsActive I ep
  · rw [ite_eq_left he, ite_eq_left he]
    congr 1
    funext value
    cases value with
    | none => rfl
    | some wr =>
        exact congrArg some (GXMSS.Interval.PRFDerived.signatureOfWord_eq_of_active_starts_eq
          hash I pp xs ys fillers hactive ep he wr)
  · rw [ite_eq_right he, ite_eq_right he]

private theorem fixedMaterialInteraction_eq_of_active_starts_eq
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (pp : PP) (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ ep, Epoch.IsActive I ep → xs ep = ys ep) :
    fixedMaterialInteraction hash enc K I adv (pp, xs, fillers) =
      fixedMaterialInteraction hash enc K I adv (pp, ys, fillers) := by
  have hpk := GXMSS.Interval.PRFDerived.publicKey_eq_of_active_starts_eq
    hash I pp xs ys fillers hactive
  have hsign : GXMSS.Interval.sign hash enc K I
      (GXMSS.Interval.keys hash I pp xs fillers).2 =
      GXMSS.Interval.sign hash enc K I (GXMSS.Interval.keys hash I pp ys fillers).2 := by
    funext ep msg
    exact directSign_eq_of_active_starts_eq hash enc K I pp xs ys fillers hactive ep msg
  have hhandler : fixedHandler (GXMSS.Interval.scheme hash enc K I)
      (GXMSS.Interval.keys hash I pp xs fillers).2 =
      fixedHandler (GXMSS.Interval.scheme hash enc K I)
        (GXMSS.Interval.keys hash I pp ys fillers).2 := by
    simp only [fixedHandler, SyncSignatureUnforgeability.signingOracle,
      GXMSS.Interval.scheme, hsign]
  unfold fixedMaterialInteraction
  dsimp only
  rw [hpk, hhandler]

private theorem activeStarts_follow_sampling {A : Type}
    [SampleableType H] (I : Interval h)
    (follow : (Fin (2 ^ h) → Fin v → H) → ProbComp A)
    (hinvariant : ∀ xs ys, (∀ ep, Epoch.IsActive I ep → xs ep = ys ep) → follow xs = follow ys) :
    (GXMSS.sampleStarts H h v >>= follow) =ᵈ
      (Fin.mOfFn (I.last.val - I.first.val + 1)
        (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H))) >>= fun active =>
        follow (GXMSS.Interval.PRFDerived.extendStarts I active)) := by
  let : MeasurableSpace H := ⊤
  have hrestrict := EvalDistEq.of_evalDist_eq (active_starts_sampling (H := H) (v := v) I)
  have hpoint : (GXMSS.sampleStarts H h v >>= follow) =
      (GXMSS.Interval.PRFDerived.restrictStarts I <$> GXMSS.sampleStarts H h v >>= fun active =>
        follow (GXMSS.Interval.PRFDerived.extendStarts I active)) := by
    rw [map_eq_bind_pure_comp]
    simp only [bind_assoc, Function.comp_apply, pure_bind]
    apply bind_congr
    intro full
    apply hinvariant full _
    intro ep he
    exact (GXMSS.Interval.PRFDerived.extendStarts_restrictStarts_active I full ep he).symm
  rw [hpoint]
  exact hrestrict.bind (fun active => EvalDistEq.rfl
    (mx := follow (GXMSS.Interval.PRFDerived.extendStarts I active)))

private theorem ideal_interaction_active_extension [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) (hfiller : UsedFillerSamplingLaw I p) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc p K I adv)).run' ∅ =ᵈ (do
        let pp ← hash.thf.seedGen
        let active ← Fin.mOfFn (I.last.val - I.first.val + 1)
          (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))
        let fillers ← sampleFillers I H
        fixedMaterialInteraction hash enc K I adv
          (pp, GXMSS.Interval.PRFDerived.extendStarts I active, fillers)) := by
  rw [adaptiveInteraction_from_material, simulateQ_bind, StateT.run'_bind']
  apply EvalDistEq.trans (my := do
    let result ← (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries I p)).run ∅
    fixedMaterialInteraction hash enc K I adv result.1)
  · apply EvalDistEq.bind_congr_of_support
    intro result hresult
    rcases result with ⟨⟨pp, starts, fillers⟩, table⟩
    dsimp only
    let pair := GXMSS.Interval.keys hash I pp starts fillers
    have hfresh := keyMaterial_ideal_cache I p ((pp, starts, fillers), table) hresult
    have hfixed := ideal_fixed_interaction_correspondence hash enc p K hretry I pair.2
      (adv.forge pair.1) SyncSignatureUnforgeability.emptyHistory table hfresh
    rw [simulateQ_bind, StateT.run'_bind']
    have hnormalize : (do
        let result ← (simulateQ (PRFScheme.prfIdealQueryImpl
          (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
          ((simulateQ (adaptiveHandler hash enc p K I pair.2) (adv.forge pair.1)).run
            SyncSignatureUnforgeability.emptyHistory)).run table
        let outcome := result.1
        (simulateQ (PRFScheme.prfIdealQueryImpl
          (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
          (pure (pair.1, outcome.1, outcome.2))).run' result.2) =
        (fun result =>
          let outcome := result.1
          (pair.1, outcome.1, outcome.2)) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl
            (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
            ((simulateQ (adaptiveHandler hash enc p K I pair.2) (adv.forge pair.1)).run
              SyncSignatureUnforgeability.emptyHistory)).run table := by
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      rcases result with ⟨⟨forgery, history⟩, retained⟩
      dsimp only
      rw [simulateQ_pure]
      rfl
    change _ =ᵈ fixedMaterialInteraction hash enc K I adv (pp, starts, fillers)
    have hout := hfixed.map (fun outcome => (pair.1, outcome.1, outcome.2))
    apply (evalDistEq_of_eq hnormalize).trans
    simp only [StateT.run'_eq, Functor.map_map] at hout
    (convert hout using 1; rfl)
  · have hdrop : (do
        let result ← (simulateQ (PRFScheme.prfIdealQueryImpl
          (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
          (keyMaterialQueries I p)).run ∅
        fixedMaterialInteraction hash enc K I adv result.1) = (do
          let material ← (simulateQ (PRFScheme.prfIdealQueryImpl
            (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
            (keyMaterialQueries I p)).run' ∅
          fixedMaterialInteraction hash enc K I adv material) := by
        simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
    rw [hdrop]
    have hmaterial := keyMaterial_ideal_sampling (M := M) hash I p hseed hstart hfiller
    simpa only [bind_assoc, pure_bind] using
      hmaterial.bind (fun material => EvalDistEq.rfl
        (mx := fixedMaterialInteraction hash enc K I adv material))

private theorem direct_interaction_active_extension [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.interaction (GXMSS.Interval.scheme hash enc K I) adv =ᵈ (do
      let pp ← hash.thf.seedGen
      let active ← Fin.mOfFn (I.last.val - I.first.val + 1)
        (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))
      let fillers ← sampleFillers I H
      fixedMaterialInteraction hash enc K I adv
        (pp, GXMSS.Interval.PRFDerived.extendStarts I active, fillers)) := by
  have hnormalize : SyncSignatureUnforgeability.interaction
      (GXMSS.Interval.scheme hash enc K I) adv = (do
        let pp ← hash.thf.seedGen
        let starts ← GXMSS.sampleStarts H h v
        let fillers ← sampleFillers I H
        fixedMaterialInteraction hash enc K I adv (pp, starts, fillers)) := by
    unfold SyncSignatureUnforgeability.interaction GXMSS.Interval.scheme GXMSS.Interval.keygen
      fixedMaterialInteraction fixedHandler
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro pp
    apply bind_congr
    intro starts
    apply bind_congr
    intro fillers
    -- The unfolded source runner returns the semireducible ExperimentResult triple.
    erw [map_eq_bind_pure_comp]
    rfl
  rw [hnormalize]
  apply EvalDistEq.bind_congr_of_support
  intro pp _
  have hfull := EvalDistEq.bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H)
    (fun starts fillers => fixedMaterialInteraction hash enc K I adv (pp, starts, fillers))
  have hactive := EvalDistEq.bind_bind_swap
    (Fin.mOfFn (I.last.val - I.first.val + 1)
      (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H)))) (sampleFillers I H)
    (fun active fillers => fixedMaterialInteraction hash enc K I adv
      (pp, GXMSS.Interval.PRFDerived.extendStarts I active, fillers))
  have hmiddle := EvalDistEq.bind_congr_of_support (sampleFillers I H)
    (fun fillers _ => activeStarts_follow_sampling I
      (fun starts => fixedMaterialInteraction hash enc K I adv (pp, starts, fillers))
      (fun xs ys hsame => fixedMaterialInteraction_eq_of_active_starts_eq
        hash enc K I adv pp xs ys fillers hsame))
  exact hfull.trans (hmiddle.trans hactive.symm)

/-- Projection laws at queried coordinates give the complete native interval ideal interaction,
retaining public key, forgery, first-request history and missing mass. -/
theorem ideal_interaction_correspondence_of_used_frontier [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) (hfiller : UsedFillerSamplingLaw I p) :
    IdealInteractionCorrespondence hash enc p K I adv := by
  unfold IdealInteractionCorrespondence
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  have hideal := ideal_interaction_active_extension hash enc p K I adv
    hseed hstart hretry hfiller
  have hdirect := direct_interaction_active_extension hash enc K I adv
  exact (hideal.trans hdirect.symm).evalDist_eq

/-- Four global projection laws imply the complete native interval idealization. -/
theorem ideal_interaction_correspondence [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) (hfiller : FillerSamplingLaw p) :
    IdealInteractionCorrespondence hash enc p K I adv := by
  exact ideal_interaction_correspondence_of_used_frontier hash enc p K I adv
    hseed hstart hretry (fun _ => hfiller)

end GXMSS.Interval.PRFDerived.Unforgeability

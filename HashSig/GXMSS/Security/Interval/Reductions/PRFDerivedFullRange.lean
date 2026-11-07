/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerivedScheme
import all HashSig.GXMSS.Interval.PRFDerivedScheme
public import HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.PRFDerivedScheme
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction
public import HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache

/-!
# Full-range PRF experiment transport

The three-family query embedding restricts complete-response caches and preserves actual
keygen, real/ideal experiments, advantage and strong-output measures independently of final bounds.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec Encoding GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory ENNReal
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Restrict the evaluator to the complete three query families, preserving the actual key law. -/
@[expose] def restrictPRF (prf : SharedPRF Key PP M Response h v) :
    GXMSS.PRFDerived.Unforgeability.SharedPRF Key PP M Response h v where
  keygen := prf.keygen
  eval key query := prf.eval key (GXMSS.Interval.PRFDerived.Query.ofComplete query)

/-- Restriction keeps the actual key generator, without a uniform-key assumption. -/
theorem restrictPRF_keygen (prf : SharedPRF Key PP M Response h v) :
    (restrictPRF prf).keygen = prf.keygen := rfl

/-- Full range has no frontier response coordinate and makes no filler function call. -/
theorem fillerQueries_full_bound
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (fillerQueries (M := M) (v := v) (Interval.full h) p pp) 0 := by
  have hbound := fillerQueries_bound (M := M) (v := v) (Interval.full h) p pp
  simpa only [Fintype.card_eq_zero] using hbound

private abbrev CompleteQuery (PP M : Type) (h v : ℕ) :=
  GXMSS.PRFDerived.Query PP M h v

private abbrev IntervalQuery (PP M : Type) (h v : ℕ) :=
  GXMSS.Interval.PRFDerived.Query PP M h v

private def embedQueryImpl : QueryImpl (PRFScheme.PRFOracleSpec (CompleteQuery PP M h v) Response)
    (OracleComp (PRFScheme.PRFOracleSpec (IntervalQuery PP M h v) Response)) :=
  fun query => match query with
    | .inl n => liftM (OracleSpec.query (Sum.inl n) :
        OracleQuery (PRFScheme.PRFOracleSpec (IntervalQuery PP M h v) Response) _)
    | .inr q => PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.ofComplete q)

private theorem embed_functionQuery (q : CompleteQuery PP M h v) :
    simulateQ (embedQueryImpl (Response := Response)) (PRFScheme.functionQuery q) =
      PRFScheme.functionQuery
        (GXMSS.Interval.PRFDerived.Query.ofComplete q) := by
  simp [embedQueryImpl, PRFScheme.functionQuery]

private theorem simulateQ_mOfFn {ι ι' A : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} (impl : QueryImpl spec (OracleComp spec'))
    (n : ℕ) (f : Fin n → OracleComp spec A) :
    simulateQ impl (Fin.mOfFn n f) = Fin.mOfFn n (fun i => simulateQ impl (f i)) := by
  induction n with
  | zero => simp only [Fin.mOfFn, simulateQ_pure]
  | succ n ih =>
      simp only [Fin.mOfFn, simulateQ_bind, simulateQ_pure]
      apply bind_congr
      intro head
      rw [ih]

private theorem pure_of_zero_total_bound {ι A : Type} {spec : OracleSpec ι}
    [Subsingleton A] (value : A) (program : OracleComp spec A)
    (hbound : IsTotalQueryBound program 0) : program = pure value := by
  induction program using OracleComp.inductionOn with
  | pure result => exact congrArg pure (Subsingleton.elim result value)
  | query_bind query next _ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      omega

private theorem fillerQueries_full_pure
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    fillerQueries (M := M) (v := v) (Interval.full h) p pp =
      pure (fun node => isEmptyElim node) := by
  let : Subsingleton (Fillers (Interval.full h) H) :=
    ⟨fun f g => funext fun node => isEmptyElim node⟩
  exact pure_of_zero_total_bound _ _ (fillerQueries_full_bound p pp)

private theorem publicSeedQuery_embed
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) :
    simulateQ (embedQueryImpl (M := M) (h := h) (v := v))
      (GXMSS.PRFDerived.Unforgeability.publicSeedQuery p.toComplete) = publicSeedQuery p := by
  simp [GXMSS.PRFDerived.Unforgeability.publicSeedQuery, publicSeedQuery, embed_functionQuery,
    GXMSS.Interval.PRFDerived.Interpretation.toComplete,
    GXMSS.Interval.PRFDerived.Query.ofComplete]

private theorem map_mOfFn_congr {ι : Type} {spec : OracleSpec ι} {A B : Type} {n m : ℕ}
    (hn : n = m) (f : Fin n → OracleComp spec A) (g : Fin m → OracleComp spec A)
    (out : (Fin n → A) → B) (out' : (Fin m → A) → B)
    (hf : ∀ i j, i.val = j.val → f i = g j)
    (hout : ∀ a b, (∀ i j, i.val = j.val → a i = b j) → out a = out' b) :
    out <$> Fin.mOfFn n f = out' <$> Fin.mOfFn m g := by
  subst m
  have hfg : f = g := funext fun i => hf i i rfl
  subst g
  congr 1
  funext a
  exact hout a a (fun i j hij => congrArg a (Fin.ext hij))

private theorem startQueries_full_embed
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    simulateQ (embedQueryImpl (M := M) (h := h) (v := v))
      (GXMSS.PRFDerived.Unforgeability.startQueries p.toComplete pp) =
      startQueries (Interval.full h) p pp := by
  have hcount : 2 ^ h - 1 + 1 = 2 ^ h :=
    Nat.sub_add_cancel (by
      have hp : 0 < 2 ^ h := by positivity
      omega)
  unfold GXMSS.PRFDerived.Unforgeability.startQueries
  change simulateQ embedQueryImpl
    ((fun starts epoch chain => starts (finProdFinEquiv (epoch, chain))) <$>
      Fin.mOfFn (2 ^ h * v) (fun index =>
        GXMSS.PRFDerived.Unforgeability.startQuery p.toComplete pp index.divNat index.modNat)) = _
  rw [simulateQ_map, simulateQ_mOfFn]
  simp only [GXMSS.PRFDerived.Unforgeability.startQuery, simulateQ_map, embed_functionQuery]
  unfold startQueries
  apply map_mOfFn_congr (congrArg (fun n => n * v) hcount.symm)
  · intro i j hij
    unfold startQuery
    congr 3
    change GXMSS.Interval.PRFDerived.Query.start pp i.divNat i.modNat =
      .start pp (GXMSS.Interval.PRFDerived.activeEpoch (Interval.full h) j.divNat)
        j.modNat
    congr 1
    · apply Fin.ext
      change i.val / v = 0 + j.val / v
      simpa only [zero_add] using congrArg (fun n => n / v) hij
    · exact Fin.ext (congrArg (fun n => n % v) hij)
  · intro a b hab
    funext ep chain
    unfold GXMSS.Interval.PRFDerived.extendStarts
    rw [dite_eq_left (Epoch.isActive_full ep)]
    apply hab
    rfl

private theorem retryQueries_embed
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (K : ℕ) (pp : PP) (ep : Fin (2 ^ h)) (msg : M) :
    simulateQ (embedQueryImpl (v := v))
      (GXMSS.PRFDerived.Unforgeability.retryQueries p.toComplete K pp ep msg) =
      retryQueries p K pp ep msg := by
  unfold GXMSS.PRFDerived.Unforgeability.retryQueries retryQueries
  change simulateQ embedQueryImpl (List.ofFn <$> Fin.mOfFn K (fun i =>
    p.retryRandomizer <$> PRFScheme.functionQuery
      (GXMSS.PRFDerived.Query.retry pp ep msg i.val))) = _
  rw [simulateQ_map, simulateQ_mOfFn]
  simp only [simulateQ_map, embed_functionQuery,
    GXMSS.Interval.PRFDerived.Query.ofComplete]
  rfl

private theorem oracleSign_full_embed (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (sk : GXMSS.Interval.SecretKey PP H h v (Interval.full h))
    (ep : Fin (2 ^ h)) (msg : M) :
    simulateQ embedQueryImpl (GXMSS.PRFDerived.Unforgeability.oracleSign
      hash enc p.toComplete K sk.complete
      ep msg) = oracleSign hash enc p K (Interval.full h) sk ep msg := by
  unfold GXMSS.PRFDerived.Unforgeability.oracleSign oracleSign
  rw [ite_eq_left (Epoch.isActive_full ep)]
  dsimp only
  rw [simulateQ_bind, retryQueries_embed]
  apply bind_congr
  intro randomizers
  rw [simulateQ_pure, GXMSS.Interval.PRFDerived.signResult_full]

private theorem adaptiveHandler_full_embed [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (sk : GXMSS.Interval.SecretKey PP H h v (Interval.full h))
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Fin (2 ^ h)) M (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ embedQueryImpl
      ((GXMSS.PRFDerived.Unforgeability.adaptiveHandler
        hash enc p.toComplete K sk.complete query).run history) =
      (adaptiveHandler hash enc p K (Interval.full h) sk query).run history := by
  cases query with
  | inl n =>
      simp [GXMSS.PRFDerived.Unforgeability.adaptiveHandler, adaptiveHandler, embedQueryImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget]
  | inr request =>
      rcases request with ⟨ep, msg⟩
      simp only [GXMSS.PRFDerived.Unforgeability.adaptiveHandler, adaptiveHandler,
        QueryImpl.add_apply_inr]
      change simulateQ embedQueryImpl
        (SyncSignatureUnforgeability.signingOracle
          (GXMSS.PRFDerived.Unforgeability.oracleScheme hash enc p.toComplete K)
          sk.complete (ep, msg) history) =
        SyncSignatureUnforgeability.signingOracle
          (oracleScheme hash enc p K (Interval.full h)) sk (ep, msg) history
      cases hused : history ep with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused),
            SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          simp
      | none =>
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused),
            SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          simp only [simulateQ_bind, simulateQ_pure]
          change (do
            let answer ← simulateQ embedQueryImpl
              (GXMSS.PRFDerived.Unforgeability.oracleSign
                hash enc p.toComplete K sk.complete ep msg)
            pure (answer, Function.update history ep (some (msg, answer)))) = (do
              let answer ← oracleSign hash enc p K (Interval.full h) sk ep msg
              pure (answer, Function.update history ep (some (msg, answer))))
          rw [oracleSign_full_embed]

private theorem adaptiveInteraction_full_embed [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ embedQueryImpl
      (GXMSS.PRFDerived.Unforgeability.adaptiveInteraction hash enc p.toComplete K adv) =
      adaptiveInteraction hash enc p K (Interval.full h) adv := by
  unfold GXMSS.PRFDerived.Unforgeability.adaptiveInteraction adaptiveInteraction
  rw [simulateQ_bind, publicSeedQuery_embed]
  apply bind_congr
  intro pp
  rw [simulateQ_bind, startQueries_full_embed]
  apply bind_congr
  intro starts
  rw [fillerQueries_full_pure, pure_bind]
  let fillers : Fillers (Interval.full h) H := fun node => isEmptyElim node
  let pair := GXMSS.Interval.keys hash (Interval.full h) pp starts fillers
  let signingKey := pair.2
  have hcomp := simulateQ_StateT_compose
    (GXMSS.PRFDerived.Unforgeability.adaptiveHandler hash enc p.toComplete K signingKey.complete)
    embedQueryImpl (adaptiveHandler hash enc p K (Interval.full h) pair.2)
    (adaptiveHandler_full_embed hash enc p K pair.2) (adv.forge pair.1)
    SyncSignatureUnforgeability.emptyHistory
  dsimp only [pair, signingKey, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.IntervalMerkle.root_full] at hcomp
  unfold SyncSignatureUnforgeability.ExperimentResult at *
  simp only [map_eq_bind_pure_comp]
  rw [simulateQ_bind]
  simp only [Prod.mk.eta, simulateQ_pure]
  convert congrArg (fun computation => (fun outcome =>
      ((GXMSS.keys hash pp starts).1, outcome.1, outcome.2)) <$> computation) hcomp using 1 <;>
    simp [map_eq_bind_pure_comp, GXMSS.Interval.keys, GXMSS.keys, GXMSS.IntervalMerkle.root_full]
  rfl

private theorem randgenPRFReduction_full_embed [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ embedQueryImpl
      (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) =
      randgenPRFReduction hash enc p K (Interval.full h) adv := by
  unfold GXMSS.PRFDerived.Unforgeability.randgenPRFReduction randgenPRFReduction
  change simulateQ embedQueryImpl (SyncSignatureUnforgeability.strongValid _ <$> _) =
    SyncSignatureUnforgeability.strongValid _ <$> _
  rw [simulateQ_map, adaptiveInteraction_full_embed]
  rfl

private def restrictCache
    (cache : ((IntervalQuery PP M h v) →ₒ Response).QueryCache) :
    ((CompleteQuery PP M h v) →ₒ Response).QueryCache :=
  QueryCache.ofFn fun q => cache (GXMSS.Interval.PRFDerived.Query.ofComplete q)

private theorem restrictCache_empty : restrictCache
    (∅ : ((IntervalQuery PP M h v) →ₒ Response).QueryCache) = ∅ := rfl

private theorem restrictCache_cacheQuery
    [DecidableEq (IntervalQuery PP M h v)] [DecidableEq (CompleteQuery PP M h v)]
    (cache : ((IntervalQuery PP M h v) →ₒ Response).QueryCache)
    (query : CompleteQuery PP M h v) (response : Response) :
    restrictCache (cache.cacheQuery
      (GXMSS.Interval.PRFDerived.Query.ofComplete query) response) =
      (restrictCache cache).cacheQuery query response := by
  apply QueryCache.ext
  intro other
  by_cases heq : other = query
  · subst other
    simp [restrictCache, QueryCache.cacheQuery_self]
  · have hne : GXMSS.Interval.PRFDerived.Query.ofComplete other ≠
        GXMSS.Interval.PRFDerived.Query.ofComplete query :=
      fun h => heq (GXMSS.Interval.PRFDerived.Query.ofComplete_injective h)
    change (cache.cacheQuery
      (GXMSS.Interval.PRFDerived.Query.ofComplete query) response)
        (GXMSS.Interval.PRFDerived.Query.ofComplete other) = _
    rw [QueryCache.cacheQuery_of_ne cache response hne,
      QueryCache.cacheQuery_of_ne (restrictCache cache) response heq]
    rfl

private theorem ideal_embed_step [SampleableType Response]
    [DecidableEq (IntervalQuery PP M h v)] [DecidableEq (CompleteQuery PP M h v)]
    (query : (PRFScheme.PRFOracleSpec (CompleteQuery PP M h v) Response).Domain)
    (cache : ((IntervalQuery PP M h v) →ₒ Response).QueryCache) :
    Prod.map id restrictCache <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := IntervalQuery PP M h v) (R := Response)) (embedQueryImpl query)).run cache =
      (PRFScheme.prfIdealQueryImpl
        (D := CompleteQuery PP M h v) (R := Response) query).run (restrictCache cache) := by
  cases query with
  | inl n =>
      simp [embedQueryImpl, PRFScheme.prfIdealQueryImpl, OracleSpec.romImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget, unifFwdImpl, Functor.map_map]
  | inr q =>
      simp only [embedQueryImpl, PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
        PRFScheme.prfIdealQueryImpl_apply_inr]
      rw [randomOracle.run_eq, randomOracle.run_eq]
      have hlookup : (restrictCache cache) q =
          cache (GXMSS.Interval.PRFDerived.Query.ofComplete q) := rfl
      rw [hlookup]
      cases hc : cache (GXMSS.Interval.PRFDerived.Query.ofComplete q) <;>
        simp [Functor.map_map, restrictCache_cacheQuery]

/-- Full-range scheme equality is a separate deterministic obligation; filler projection laws
are absent because no filler response is evaluated at full range. -/
@[expose] def FullRangeSchemeCorrespondence [SampleableType Key] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) : Prop :=
  GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K (Interval.full h) =
    GXMSS.PRFDerived.scheme hash enc (restrictPRF prf).eval p.toComplete K

/-- Equality of real PRF experiment measures under the explicit query embedding. -/
@[expose] def FullRangeRealCorrespondence [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : Prop :=
  𝒟[prf.prfRealExperiment (randgenPRFReduction hash enc p K (Interval.full h) adv)] =
    𝒟[(restrictPRF prf).prfRealExperiment
      (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv)]

/-- Equality of cached ideal experiment measures under the same query embedding. -/
@[expose] def FullRangeIdealCorrespondence [SampleableType Response]
    [DecidableEq H] [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : Prop :=
  𝒟[PRFScheme.prfIdealExperiment (randgenPRFReduction hash enc p K (Interval.full h) adv)] =
    𝒟[PRFScheme.prfIdealExperiment
      (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv)]

/-- Deterministic full-range scheme correspondence needs no filler projection law. -/
theorem fullRangeSchemeCorrespondence [SampleableType Key] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ) :
    FullRangeSchemeCorrespondence hash enc prf p K :=
  GXMSS.Interval.PRFDerived.scheme_full hash enc prf.eval p K

/-- Full-range real PRF experiments agree for the actual retained key generator and evaluator.
No key distribution or response projection law is required. -/
theorem fullRangeRealCorrespondence [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    FullRangeRealCorrespondence hash enc prf p K adv := by
  unfold FullRangeRealCorrespondence PRFScheme.prfRealExperiment
  apply congrArg evalDist
  change (prf.keygen >>= _) = (prf.keygen >>= _)
  apply bind_congr
  intro key
  rw [← randgenPRFReduction_full_embed, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  cases query with
  | inl n =>
      simp [QueryImpl.compose, embedQueryImpl, PRFScheme.prfRealQueryImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget]
  | inr q =>
      simp [QueryImpl.compose, embedQueryImpl, restrictPRF]

/-- Full-range lazy ideal PRF experiments agree through a cache restriction that preserves every
hit and fresh draw. The result assumes no response projection sampling laws. -/
theorem fullRangeIdealCorrespondence [SampleableType Response]
    [DecidableEq H] [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    FullRangeIdealCorrespondence hash enc p K adv := by
  unfold FullRangeIdealCorrespondence PRFScheme.prfIdealExperiment
  rw [← randgenPRFReduction_full_embed, ← QueryImpl.simulateQ_compose]
  apply congrArg evalDist
  exact run'_simulateQ_eq_of_query_map_eq
    (QueryImpl.compose PRFScheme.prfIdealQueryImpl embedQueryImpl)
    PRFScheme.prfIdealQueryImpl restrictCache ideal_embed_step
    (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) ∅

/-- The two actual PRF experiments give equal distinguishing advantages without any key or
response projection sampling law. -/
theorem fullRangePRFAdvantage [SampleableType Response] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) =
      (restrictPRF prf).prfAdvantage
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) := by
  have hreal := fullRangeRealCorrespondence hash enc prf p K adv
  have hideal := fullRangeIdealCorrespondence hash enc p K adv
  unfold FullRangeRealCorrespondence at hreal
  unfold FullRangeIdealCorrespondence at hideal
  unfold PRFScheme.prfAdvantage
  rw [hreal, hideal]

/-- Full-range strong experiment measures agree from exact scheme equality, without any
response projection sampling law. -/
theorem fullRangeStrongExperiment [SampleableType Key] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K (Interval.full h))
      ProbCompRuntime.probComp adv = SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.PRFDerived.scheme hash enc (restrictPRF prf).eval p.toComplete K)
        ProbCompRuntime.probComp adv := by
  exact congrArg (fun alg => SyncSignatureUnforgeability.strongUnforgeableExp
    alg ProbCompRuntime.probComp adv) (fullRangeSchemeCorrespondence hash enc prf p K)

end GXMSS.Interval.PRFDerived.Unforgeability

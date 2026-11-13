/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedOracleInteraction
public import VCVio.CryptoFoundations.PRF.DomainTransport

/-!
# Three-family complete PRF interaction

The full-range interval program uses only complete coordinates. Its retraction to the original
three-family interface preserves entire programs and native experiments, with no filler law.
-/

public section
namespace GXMSS.PRFDerived.Unforgeability
open OracleComp OracleSpec GXMSS GXMSS.IntervalMerkle
open PRFScheme.DomainTransport
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Keep complete coordinates; unused frontier coordinates retract to the seed coordinate. -/
@[expose] def projectQuery : GXMSS.Interval.PRFDerived.Query PP M h v →
    GXMSS.PRFDerived.Query PP M h v
  | .complete query => query
  | .filler .. => .publicSeed

/-- An auxiliary frontier projection; full range never observes it. -/
@[expose] def intervalProjection (p : GXMSS.PRFDerived.Interpretation PP H R Response) :
    GXMSS.Interval.PRFDerived.Interpretation PP H R Response where
  toComplete := p
  fillerDigest := p.chainStart

private def completeQuery :
    (ℕ ⊕ GXMSS.Interval.PRFDerived.Query PP M h v) → Prop
  | .inl _ => True
  | .inr (.complete _) => True
  | .inr (.filler ..) => False

private theorem startQueries_complete (p : GXMSS.PRFDerived.Interpretation PP H R Response)
    (pp : PP) :
    AllQueriesSatisfy
      (GXMSS.Interval.PRFDerived.Unforgeability.startQueries (M := M) (v := v)
        (Interval.full h) (intervalProjection p) pp) completeQuery := by
  unfold GXMSS.Interval.PRFDerived.Unforgeability.startQueries
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply allQueriesSatisfy_fin_mOfFn _ completeQuery
  intro index
  unfold GXMSS.Interval.PRFDerived.Unforgeability.startQuery PRFScheme.functionQuery
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  rw [allQueriesSatisfy_query_iff]
  trivial

private theorem fillerQueries_complete
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    AllQueriesSatisfy
      (GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries (M := M) (v := v)
        (Interval.full h) (intervalProjection p) pp) completeQuery := by
  have hz := GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries_bound
    (M := M) (v := v) (Interval.full h) (intervalProjection p) pp
  simp only [Fintype.card_of_isEmpty] at hz
  obtain ⟨fillers, hfillers⟩ := isTotalQueryBound_zero_iff.mp hz
  rw [hfillers]
  exact allQueriesSatisfy_pure _ _

private theorem oracleSign_complete (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.Interval.SecretKey PP H h v (Interval.full h))
    (ep : Fin (2 ^ h)) (message : M) :
    AllQueriesSatisfy
      (GXMSS.Interval.PRFDerived.Unforgeability.oracleSign hash enc (intervalProjection p)
        budget (Interval.full h) core ep message) completeQuery := by
  unfold GXMSS.Interval.PRFDerived.Unforgeability.oracleSign
  split
  · dsimp only
    apply allQueriesSatisfy_bind _ (fun _ => allQueriesSatisfy_pure _ _)
    unfold GXMSS.Interval.PRFDerived.Unforgeability.retryQueries
      PRFScheme.ProjectedQueries.responseQueries
    rw [allQueriesSatisfy_def]
    apply (isQueryBound_map_iff _ _ _ _ _).mpr
    rw [← allQueriesSatisfy_def]
    apply allQueriesSatisfy_fin_mOfFn _ completeQuery
    intro attempt
    unfold PRFScheme.functionQuery
    rw [allQueriesSatisfy_def]
    apply (isQueryBound_map_iff _ _ _ _ _).mpr
    rw [← allQueriesSatisfy_def]
    rw [allQueriesSatisfy_query_iff]
    trivial
  · exact allQueriesSatisfy_pure _ _

private theorem handler_complete [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.Interval.SecretKey PP H h v (Interval.full h))
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M (Signature R H h v)) :
    AllQueriesSatisfy
      ((GXMSS.Interval.PRFDerived.Unforgeability.adaptiveHandler hash enc
        (intervalProjection p) budget (Interval.full h) core query).run history)
      completeQuery := by
  cases query with
  | inl n =>
      suffices hforward : AllQueriesSatisfy
          ((fun response => (response, history)) <$>
            (liftM (OracleSpec.query (Sum.inl n) : OracleQuery
              (PRFScheme.PRFOracleSpec (GXMSS.Interval.PRFDerived.Query PP M h v)
                Response) _) : OracleComp _ _)) completeQuery by
        simpa [GXMSS.Interval.PRFDerived.Unforgeability.adaptiveHandler,
          SyncSignatureUnforgeability.PRFSimulation.signingHandler, QueryImpl.liftTarget]
          using hforward
      rw [allQueriesSatisfy_def]
      apply (isQueryBound_map_iff _ _ _ _ _).mpr
      rw [← allQueriesSatisfy_def, allQueriesSatisfy_query_iff]
      trivial
  | inr request =>
      rcases request with ⟨ep, message⟩
      change AllQueriesSatisfy (SyncSignatureUnforgeability.signingOracle
        (GXMSS.Interval.PRFDerived.Unforgeability.oracleScheme hash enc
          (intervalProjection p) budget (Interval.full h)) core (ep, message) history)
        completeQuery
      cases hused : history ep with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          exact allQueriesSatisfy_pure _ _
      | none =>
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          apply allQueriesSatisfy_bind (oracleSign_complete hash enc p budget core ep message)
            (fun _ => allQueriesSatisfy_pure _ _)

/-- The full adaptive program issues no frontier query, without a signing-budget premise. -/
theorem fullRange_interaction_complete [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    AllQueriesSatisfy
      (GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
        (intervalProjection p) budget (Interval.full h) adv)
      (fun query => ∀ input, query = Sum.inr input →
        GXMSS.Interval.PRFDerived.Query.ofComplete (projectQuery input) = input) := by
  suffices hcomplete : AllQueriesSatisfy
      (GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
        (intervalProjection p) budget (Interval.full h) adv) completeQuery by
    apply hcomplete.mono
    rintro (n | input) hquery input' heq
    · cases heq
    · cases input with
      | complete query =>
          cases heq
          rfl
      | filler pp level index => exact hquery.elim
  unfold GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction
  apply allQueriesSatisfy_bind
  · unfold GXMSS.Interval.PRFDerived.Unforgeability.publicSeedQuery PRFScheme.functionQuery
    rw [allQueriesSatisfy_def]
    apply (isQueryBound_map_iff _ _ _ _ _).mpr
    rw [← allQueriesSatisfy_def]
    rw [allQueriesSatisfy_query_iff]
    trivial
  intro pp
  apply allQueriesSatisfy_bind (startQueries_complete p pp)
  intro starts
  apply allQueriesSatisfy_bind (fillerQueries_complete p pp)
  intro fillers
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply (allQueriesSatisfy_of_forall (fun _ => True.intro) _).simulateQ_run
  intro query _ history
  exact handler_complete hash enc p budget _ query history

/-- The complete interaction uses the original three-family PRF interface. -/
@[expose] noncomputable def adaptiveInteraction [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :=
  simulateQ (inputMap projectQuery)
    (GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
      (intervalProjection p) budget (Interval.full h) adv)

/-- Embedding the complete interaction recovers the entire full-range interval program. -/
theorem adaptiveInteraction_fullRange [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (inputMap GXMSS.Interval.PRFDerived.Query.ofComplete)
      (adaptiveInteraction hash enc p budget adv) =
    GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
      (intervalProjection p) budget (Interval.full h) adv := by
  exact inputMap_roundtrip _ _ _ (fullRange_interaction_complete hash enc p budget adv)

/-- A Boolean observation of the original three-family interaction. -/
@[expose] noncomputable def randgenPRFReduction [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    PRFScheme.PRFAdversary (GXMSS.PRFDerived.Query PP M h v) Response :=
  let run := adaptiveInteraction hash enc p budget adv
  run.map (SyncSignatureUnforgeability.strongValid
    (GXMSS.Interval.PRFDerived.Unforgeability.oracleScheme hash enc
      (intervalProjection p) budget (Interval.full h)))

/-- Embedding the native three-family distinguisher recovers its full-range interval program. -/
theorem randgenPRFReduction_fullRange [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (inputMap GXMSS.Interval.PRFDerived.Query.ofComplete)
      (randgenPRFReduction hash enc p budget adv) =
    GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc
      (intervalProjection p) budget (Interval.full h) adv := by
  let observe := SyncSignatureUnforgeability.strongValid
    (GXMSS.Interval.PRFDerived.Unforgeability.oracleScheme hash enc
      (intervalProjection p) budget (Interval.full h))
  change simulateQ (inputMap GXMSS.Interval.PRFDerived.Query.ofComplete)
      (observe <$> adaptiveInteraction hash enc p budget adv) =
    observe <$> GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
      (intervalProjection p) budget (Interval.full h) adv
  rw [simulateQ_map, adaptiveInteraction_fullRange]

/-- Retraction of the interval distinguisher is exactly the original-domain distinguisher. -/
theorem randgenPRFReduction_project [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    randgenPRFReduction hash enc p budget adv =
      simulateQ (inputMap projectQuery)
        (GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc
          (intervalProjection p) budget (Interval.full h) adv) := by
  let observe := SyncSignatureUnforgeability.strongValid
    (GXMSS.Interval.PRFDerived.Unforgeability.oracleScheme hash enc
      (intervalProjection p) budget (Interval.full h))
  change observe <$> simulateQ (inputMap projectQuery)
      (GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
        (intervalProjection p) budget (Interval.full h) adv) =
    simulateQ (inputMap projectQuery)
      (observe <$> GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
        (intervalProjection p) budget (Interval.full h) adv)
  exact (simulateQ_map _ _ _).symm

/-- The original-domain ideal game is the full-range interval ideal game as a whole program. -/
theorem randgenPRFReduction_ideal_fullRange [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [SampleableType Response]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    PRFScheme.prfIdealExperiment (randgenPRFReduction hash enc p budget adv) =
      PRFScheme.prfIdealExperiment
        (GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc
          (intervalProjection p) budget (Interval.full h) adv) := by
  have hmap := ideal_experiment GXMSS.Interval.PRFDerived.Query.ofComplete
    GXMSS.Interval.PRFDerived.Query.ofComplete_injective
    (randgenPRFReduction hash enc p budget adv)
  rw [randgenPRFReduction_fullRange] at hmap
  exact hmap.symm

/-- The actual complete seed-only scheme agrees with its full-range interval assembly. -/
theorem scheme_fullRange [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) :
    GXMSS.Interval.PRFDerived.scheme (pullback prf projectQuery).keygen hash enc
        (pullback prf projectQuery).eval (intervalProjection p) budget (Interval.full h) =
      GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget := by
  exact GXMSS.Interval.PRFDerived.scheme_full prf.keygen hash enc
    (pullback prf projectQuery).eval (intervalProjection p) budget

/-- The native real game uses the original evaluator and its captured key generator. -/
theorem randgenPRFReduction_real_strong [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfRealExperiment (randgenPRFReduction hash enc p budget adv) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget) adv := by
  rw [randgenPRFReduction_project, real_experiment]
  rw [GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction_real_strong]
  rw [scheme_fullRange]

/-- Native PRF advantages agree under the explicit full-range query embedding. -/
theorem randgenPRFReduction_advantage_fullRange [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [SampleableType Response]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage
        (GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc
          (intervalProjection p) budget (Interval.full h) adv) =
      (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete).prfAdvantage
        (randgenPRFReduction hash enc p budget adv) := by
  rw [← randgenPRFReduction_fullRange]
  exact advantage prf _ GXMSS.Interval.PRFDerived.Query.ofComplete_injective _

/-- One seed, every complete-tree start and the full retry budget of every signing request. -/
@[expose] def functionQueryCount (h v qs budget : ℕ) : ℕ :=
  1 + 2 ^ h * v + qs * budget

/-- Full range removes all frontier calls from the named interval count, including height zero. -/
theorem functionQueryCount_fullRange (h v qs budget : ℕ) :
    GXMSS.Interval.PRFDerived.Unforgeability.functionQueryCount
        (Interval.full h) v qs budget = functionQueryCount h v qs budget := by
  simp [GXMSS.Interval.PRFDerived.Unforgeability.functionQueryCount,
    GXMSS.Interval.PRFDerived.Unforgeability.keyMaterialQueryCount, functionQueryCount]

/-- The complete distinguisher charges every signing request and every eager retry coordinate. -/
theorem randgenPRFReduction_functionQuery_bound [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : SyncSignatureUnforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc p budget adv)
      (fun query => query.isRight = true) (functionQueryCount h v qs budget) := by
  rw [randgenPRFReduction_project, functionQuery_bound_iff]
  rw [← functionQueryCount_fullRange]
  exact GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound
    hash enc (intervalProjection p) budget qs (Interval.full h) adv hbound

private theorem fillerQueries_full_congr
    (p q : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries (M := M) (v := v)
        (Interval.full h) p pp =
      GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries
        (Interval.full h) q pp := by
  have hp := GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries_bound
    (M := M) (v := v) (Interval.full h) p pp
  have hq := GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries_bound
    (M := M) (v := v) (Interval.full h) q pp
  simp only [Fintype.card_of_isEmpty] at hp hq
  obtain ⟨left, hleft⟩ := isTotalQueryBound_zero_iff.mp hp
  obtain ⟨right, hright⟩ := isTotalQueryBound_zero_iff.mp hq
  rw [hleft, hright]
  congr 1
  funext node
  exact isEmptyElim node

/-- The whole full-range interaction is independent of its unused filler projection. -/
theorem adaptiveInteraction_fullRange_projection [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc p budget
        (Interval.full h) adv =
      GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
        (intervalProjection p.toComplete) budget (Interval.full h) adv := by
  unfold GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [fillerQueries_full_congr p (intervalProjection p.toComplete)]
  rfl

/-- The actual interval distinguisher at full range is the embedded three-family program. -/
theorem randgenPRFReduction_fullRange_projection [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (inputMap GXMSS.Interval.PRFDerived.Query.ofComplete)
        (randgenPRFReduction hash enc p.toComplete budget adv) =
      GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc p
        budget (Interval.full h) adv := by
  rw [randgenPRFReduction_fullRange]
  let observe := SyncSignatureUnforgeability.strongValid
    (GXMSS.Interval.PRFDerived.Unforgeability.oracleScheme hash enc p budget (Interval.full h))
  change observe <$> GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc
      (intervalProjection p.toComplete) budget (Interval.full h) adv =
    observe <$> GXMSS.Interval.PRFDerived.Unforgeability.adaptiveInteraction hash enc p
      budget (Interval.full h) adv
  rw [adaptiveInteraction_fullRange_projection hash enc p]

/-- Full-range native advantage transport for an arbitrary interval response interpretation. -/
theorem randgenPRFReduction_advantage_fullRange_projection [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [SampleableType Response]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage
        (GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc p
          budget (Interval.full h) adv) =
      (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete).prfAdvantage
        (randgenPRFReduction hash enc p.toComplete budget adv) := by
  rw [← randgenPRFReduction_fullRange_projection]
  exact advantage prf _ GXMSS.Interval.PRFDerived.Query.ofComplete_injective _

end GXMSS.PRFDerived.Unforgeability

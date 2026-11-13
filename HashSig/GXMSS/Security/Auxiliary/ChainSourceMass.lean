/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Selected chain source probabilities

Uniform selector probabilities and source winning masses are related by exact finite-cardinality
laws. Start resampling and filtered zero-cut identities support the native chain hybrid.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- One uniform selector succeeds with exactly inverse-cardinality probability on each returned
Game 4 win under the explicit no-maximum-output premise. -/
theorem jointChainGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      jointChainObservation hash enc K (guess, out) = true] =
      if gameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hwin : gameFourObservation hash enc K out = true
  · obtain ⟨target, htarget⟩ :=
      jointChainObservation_singleton hash enc K adv hnonmax out hout hwin
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · have hfalse : gameFourObservation hash enc K out = false := by
      cases h : gameFourObservation hash enc K out <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ite_false]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff
      (fun guess : Guess h w v => jointChainObservation hash enc K (guess, out) = true)).2
    intro guess hguess
    exact hwin (jointChainObservation_implies_gameFour hash enc K guess out hguess)
/-- Conditional on one returned source result, the actual uniform Game 5 guess passes with
exactly inverse-cardinality mass when that result is a successful Game 4 win. -/
theorem gameFiveGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      gameFiveObservation hash enc K (guess, out) = true] =
      if successfulGameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hwin : successfulGameFourObservation hash enc K out = true
  · obtain ⟨msg, sig, honestWord, forgedWord, i, hsource, hhonest, hforged, hi⟩ :=
      successfulGameFour_designated_coordinate hash enc K adv out hout hwin
    obtain ⟨target, htarget⟩ := gameFiveObservation_successful_singleton
      hash enc K out msg sig honestWord forgedWord i hsource hhonest hforged hi
      (by simpa [successfulGameFourObservation, hsource] using hwin)
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · have hfalse : successfulGameFourObservation hash enc K out = false := by
      cases h : successfulGameFourObservation hash enc K out <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ite_false]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff
      (fun guess : Guess h w v => gameFiveObservation hash enc K (guess, out) = true)).2
    intro guess hguess
    exact hwin (gameFiveObservation_implies_successfulGameFour
      hash enc K guess out hguess)
/-- The actual Game 5 native returned winning mass is exactly the successful-record Game 4
mass divided by the finite guess count. The source program's unreturned mass is unchanged. -/
theorem gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFiveAdvantage hash enc K hv hw adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ *
        successfulGameFourMass hash enc K adv := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  let source := sourceProgram hash enc K adv
  let c : ℝ≥0∞ := (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹
  have hmass : successfulGameFourMass hash enc K adv =
      𝒟[source] {out | successfulGameFourObservation hash enc K out = true} := by
    simp only [successfulGameFourMass, ProbCompRuntime.probComp_evalDist]
    rw [evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hswap :
      𝒟[gameFiveObservation hash enc K <$> gameFive hash enc K hv hw adv] =
        𝒟[do
          let out ← source
          let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
          return gameFiveObservation hash enc K (guess, out)] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  have hconditional : ∀ out ∈ support source,
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return gameFiveObservation hash enc K (guess, out)] {true} =
        if successfulGameFourObservation hash enc K out = true then c else 0 := by
    intro out hout
    have hprob := gameFiveGuess_probability hash enc K adv out hout
    have hobs : Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
        gameFiveObservation hash enc K (guess, out) = true] =
        𝒟[(fun guess => gameFiveObservation hash enc K (guess, out)) <$>
          ($ᵗ (Guess h w v) : ProbComp (Guess h w v))] {true} := by
      exact (prEvent_map _ (fun guess => gameFiveObservation hash enc K (guess, out))
        (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  have hae : ∀ᵐ out ∂𝒟[source],
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return gameFiveObservation hash enc K (guess, out)] {true} =
        if successfulGameFourObservation hash enc K out = true then c else 0 :=
    evalDist.ae_of_forall_mem_support source _ MeasurableSet.of_discrete hconditional
  unfold gameFiveAdvantage gameFiveOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist, hswap, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_congr_ae hae]
  have hfun : (fun out : Result PP H M R h v =>
      if successfulGameFourObservation hash enc K out = true then c else 0) =
      ({out | successfulGameFourObservation hash enc K out = true} : Set _).indicator
        (fun _ => c) := by
    funext out
    by_cases h : successfulGameFourObservation hash enc K out = true <;> simp [h]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
    ← hmass]
/-- On successful returned Game 4 records, the exact finite guess factor recovers the native
Game 4 mass from the actual Game 5 returned winning mass. -/
theorem successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    successfulGameFourMass hash enc K adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        gameFiveAdvantage hash enc K hv hw adv := by
  have hcard : 0 < Fintype.card (Guess h w v) := by
    rw [guess_cardinality]
    have hpow : 0 < 2 ^ h := pow_pos (by omega) _
    have hposition : 0 < 2 ^ w - 1 := by
      have := Nat.one_lt_two_pow (by omega : w ≠ 0)
      omega
    positivity
  have hne : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard
  have htop : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  rw [gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    hash enc K hv hw adv, ENNReal.mul_inv_cancel_left hne htop]
/-- Filtering preserves exactly the selected true mass of a fixed spliced adaptive run. -/
private theorem runContextSpliced_selectedMass_eq_filtered
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (observe : Result PP H M R h v → Bool)
    (hobserve : ∀ out, observe out = true →
      badSelectedHistory enc out.pk.seed selector out.history = false) :
    𝒟[(fun out => observe out) <$>
      runContextSpliced hash enc K ctx adv pp splice answer starts] {true} =
    𝒟[(fun out => out.elim false
      (fun result => observe result)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts] {true} := by
  classical
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let original : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints
  let filtered : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts endpoints
  let raw := (simulateQ original (adv.forge pk)).run
    SyncSignatureUnforgeability.emptyHistory
  let rawFiltered := (simulateQ filtered (adv.forge pk)).run
    (some SyncSignatureUnforgeability.emptyHistory)
  let event : SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) → Bool :=
    fun z => observe ⟨pk, sk, z.1, z.2⟩
  let bad := badSelectedHistory (H := H) enc pp selector
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.History (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    Option (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))) := ⊤
  have hgood : ∀ z, event z = true → bad z.2 = false := by
    intro z hz
    have h := hobserve
      (⟨pk, sk, z.1, z.2⟩ : Result PP H M R h v) hz
    simpa [bad, pk] using h
  have hpoint : ∀ z, bad z.2 = false →
      𝒟[raw] {z} = 𝒟[rawFiltered] {(z.1, some z.2)} := by
    intro z hz
    simpa only [← prEvent_eq_evalDist_singleton, raw, rawFiltered, original, filtered,
      endpoints, pk, bad] using
      contextSplicedFiltered_good_raw_output hash enc K ctx adv pp selector splice answer
        starts z.1 z.2 hz
  have heq := goodEvent_eq_filtered raw rawFiltered bad event hgood hpoint
  convert heq using 1
  · simp only [runContextSpliced, raw, event, original, endpoints, pk, sk,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · simp only [runContextFilteredSpliced, rawFiltered, event, filtered, endpoints,
      pk, sk, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro x
    cases x.2 <;> rfl
private theorem runSpliced_selectedMass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) :
    𝒟[(fun out => jointChainObservation hash enc K (selector, out)) <$>
      runSpliced hash enc K adv pp splice answer starts] {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts] {true} := by
  exact runContextSpliced_selectedMass_eq_filtered hash enc K (completeChainContext hash)
    adv pp selector splice answer starts
    (fun out => jointChainObservation hash enc K (selector, out))
    (jointChainObservation_not_badSelectedHistory hash enc K selector)
/-- The nested finite start sampler has the uniform product measure on complete arrays. -/
private theorem sampleStarts_uniform_measure [SampleableType H]
    [MeasurableSpace H] [MeasurableSingletonClass H] :
    𝒟[GXMSS.sampleStarts H h v] = ProbabilityTheory.uniformOn Set.univ := by
  classical
  unfold GXMSS.sampleStarts
  exact evalDist_mOfFn_const_uniform (2 ^ h)
    (Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H)))
    (evalDist_mOfFn_const_uniform v ($ᵗ H)
      SampleableType.evalDist_uniformSample)
/-- Refreshing one independent start coordinate preserves the complete start-array measure. -/
private theorem sampleStarts_coordinate_resampling [SampleableType H]
    (ep : Epoch h) (i : Fin v) :
    let : MeasurableSpace H := ⊤
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      return Function.update starts ep (Function.update (starts ep) i x)] =
      𝒟[GXMSS.sampleStarts H h v] := by
  classical
  let : MeasurableSpace H := ⊤
  let Flat := Epoch h × Fin v → H
  let Nested := Epoch h → Fin v → H
  let e : Flat ≃ Nested := Equiv.curry (Epoch h) (Fin v) H
  have hvalue : 𝒟[($ᵗ H : ProbComp H)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hflat : 𝒟[($ᵗ Flat : ProbComp Flat)] =
      ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hnested : 𝒟[GXMSS.sampleStarts H h v] =
      ProbabilityTheory.uniformOn Set.univ := sampleStarts_uniform_measure
  have hmap : 𝒟[e <$> ($ᵗ Flat : ProbComp Flat)] =
      𝒟[GXMSS.sampleStarts H h v] := by
    rw [evalDist_map_of_discrete, hflat,
      ProbabilityTheory.uniformOn_univ_map_equiv e, hnested]
  have hupdate : ∀ (g : Flat) (x : H),
      e (Function.update g (ep, i) x) =
        Function.update (e g) ep (Function.update (e g ep) i x) := by
    intro g x
    funext ep' i'
    change Function.update g (ep, i) x (ep', i') =
      Function.update (e g) ep (Function.update (e g ep) i x) ep' i'
    by_cases hep : ep' = ep
    · subst ep'
      by_cases hi : i' = i
      · subst i'; simp [Function.update]
      · simp [Function.update, hi]
        rfl
    · simp [Function.update, hep]
      rfl
  have hflatUpdate := evalDist_bind_bind_update
    ($ᵗ H : ProbComp H) ($ᵗ Flat : ProbComp Flat)
    hvalue hflat (ep, i) (fun g => pure (e g))
  have hinner (x : H) :
      𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
        pure (Function.update starts ep (Function.update (starts ep) i x))] =
      𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g =>
        pure (e (Function.update g (ep, i) x))] := by
    have hcross := evalDist_bind_bijective_uniform_cross
      ($ᵗ Flat : ProbComp Flat) (GXMSS.sampleStarts H h v)
      hflat hnested e e.bijective
      (fun starts => pure
        (Function.update starts ep (Function.update (starts ep) i x)))
    simp_rw [← hupdate] at hcross
    exact hcross.symm
  calc
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      return Function.update starts ep (Function.update (starts ep) i x)]
        = 𝒟[do
          let x ← ($ᵗ H : ProbComp H)
          let g ← ($ᵗ Flat : ProbComp Flat)
          return e (Function.update g (ep, i) x)] := by
            rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
            simp_rw [hinner]
    _ = 𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g => pure (e g)] := hflatUpdate
    _ = 𝒟[GXMSS.sampleStarts H h v] := by
      rw [map_eq_bind_pure_comp] at hmap
      exact hmap
/-- The refreshed start law remains equal under any returned continuation, including loss. -/
private theorem sampleStarts_coordinate_resampling_bind [SampleableType H]
    {α : Type} [MeasurableSpace α]
    (ep : Epoch h) (i : Fin v)
    (f : (Epoch h → Fin v → H) → ProbComp α) :
    let : MeasurableSpace H := ⊤
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      f (Function.update starts ep (Function.update (starts ep) i x))] =
    𝒟[GXMSS.sampleStarts H h v >>= f] := by
  classical
  let : MeasurableSpace H := ⊤
  have hrefresh := sampleStarts_coordinate_resampling (H := H) ep i
  have hprogram :
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        f (Function.update starts ep (Function.update (starts ep) i x))) =
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        pure (Function.update starts ep (Function.update (starts ep) i x))) >>= f := by
    simp only [bind_assoc, pure_bind]
  rw [hprogram, evalDist_bind_of_discrete, hrefresh,
    ← evalDist_bind_of_discrete]
/-- Pointwise equality of returned event masses integrates over a common discrete draw. -/
private theorem evalDist_bind_event_eq_of_discrete
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (event : Set β) (hevent : MeasurableSet event)
    (hfg : ∀ a, 𝒟[f a] event = 𝒟[g a] event) :
    𝒟[mx >>= f] event = 𝒟[mx >>= g] event := by
  apply le_antisymm
  · exact evalDist_bind_apply_mono_of_discrete mx f g hevent
      (fun a => (hfg a).le)
  · exact evalDist_bind_apply_mono_of_discrete mx g f hevent
      (fun a => (hfg a).ge)
/-- A position-zero splice never reads its old selected start at any positive chain position. -/
private theorem splicedChainValue_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (i : Fin v) (position : ℕ)
    (hzero : (guessedPosition guess).val = 0) (hpos : 0 < position) :
    splicedChainValue hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      ep i position =
    splicedChainValue hash pp guess answer starts ep i position := by
  unfold splicedChainValue
  by_cases htarget : ep = guessedEpoch guess ∧ i = guessedChain guess
  · have hnot : ¬position < (guessedPosition guess).val + 1 := by omega
    simp [htarget, hnot]
  · have hstart :
        Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)
          ep i = starts ep i := by
      by_cases he : ep = guessedEpoch guess
      · subst ep
        have hi : i ≠ guessedChain guess := by
          intro hi; exact htarget ⟨rfl, hi⟩
        simp [Function.update, hi]
      · simp [Function.update, he]
    simp [htarget, hstart]
/-- Updating the old selected start leaves the endpoint array of a zero splice fixed. -/
private theorem splicedEndpoints_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1) :
    splicedEndpoints hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)) =
      splicedEndpoints hash pp guess answer starts := by
  funext ep i
  exact splicedChainValue_zero_start_update hash pp guess answer starts x ep i
    (2 ^ w - 1) hzero hn
/-- Every surviving selected-epoch signature at a zero splice has a positive selected digit. -/
private theorem contextSplicedSignatureOfWord_zero_start_update
    (hash : HashInstance PP T X H h w v) (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hword : ep = guessedEpoch guess →
      0 < (wr.1 (guessedChain guess)).val) :
    contextSplicedSignatureOfWord hash ctx pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) ep wr =
    contextSplicedSignatureOfWord hash ctx pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) ep wr := by
  rw [splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn]
  have hots : (fun i => splicedChainValue hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      ep i (wr.1 i)) =
      (fun i => splicedChainValue hash pp guess answer starts ep i (wr.1 i)) := by
    funext i
    by_cases ht : ep = guessedEpoch guess ∧ i = guessedChain guess
    · exact splicedChainValue_zero_start_update hash pp guess answer starts x ep i
        (wr.1 i) hzero (by simpa only [ht.2] using hword ht.1)
    · unfold splicedChainValue
      have hstart :
          Function.update starts (guessedEpoch guess)
            (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)
            ep i = starts ep i := by
        by_cases he : ep = guessedEpoch guess
        · subst ep
          have hi : i ≠ guessedChain guess := by
            intro hi; exact ht ⟨rfl, hi⟩
          simp [Function.update, hi]
        · simp [Function.update, he]
      simp [ht, hstart]
  simp only [contextSplicedSignatureOfWord, hots]
/-- At a zero splice the filtered signing handler is independent of the old selected start. -/
private theorem contextFilteredSplicedSigningOracle_zero_start_update
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (pp : PP) (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) =
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess answer starts
      (splicedEndpoints hash pp guess answer starts) := by
  rw [splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn]
  funext q state
  cases state with
  | none => rfl
  | some history =>
    rcases q with ⟨ep, msg⟩
    by_cases hused : history ep = none
    · by_cases hactive : ctx.activity ep = true
      · simp only [contextFilteredSplicedSigningOracle, hused, hactive, ↓reduceIte]
        apply bind_congr
        intro wr
        cases wr with
        | none => rfl
        | some value =>
          by_cases hbad : ep = guessedEpoch selector ∧
              (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1
          · simp [hbad]
          · have hword : ep = guessedEpoch guess →
                0 < (value.1 (guessedChain guess)).val := by
              intro hep
              have hnot : ¬(value.1 (guessedChain selector)).val <
                  (guessedPosition selector).val + 1 := by
                intro hlt; exact hbad ⟨by simpa only [hepoch] using hep, hlt⟩
              rw [hchain] at hnot
              omega
            have hsig := contextSplicedSignatureOfWord_zero_start_update hash ctx pp guess answer
              starts x ep value hzero hn hword
            rw [splicedEndpoints_zero_start_update hash pp guess answer starts x
              hzero hn] at hsig
            simp only [hsig]
      · simp [contextFilteredSplicedSigningOracle, hused, hactive]
    · cases hrecord : history ep with
      | none => exact False.elim (hused hrecord)
      | some record => simp [contextFilteredSplicedSigningOracle, hrecord]
private theorem splicedSignatureOfWord_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hword : ep = guessedEpoch guess →
      0 < (wr.1 (guessedChain guess)).val) :
    splicedSignatureOfWord hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) ep wr =
    splicedSignatureOfWord hash pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) ep wr := by
  exact contextSplicedSignatureOfWord_zero_start_update hash (completeChainContext hash)
    pp guess answer starts x ep wr hzero hn hword
/-- At a zero splice the filtered signing handler is independent of the old selected start. -/
private theorem filteredSplicedSigningOracle_zero_start_update
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    filteredSplicedSigningOracle hash enc K pp selector guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) =
    filteredSplicedSigningOracle hash enc K pp selector guess answer starts
      (splicedEndpoints hash pp guess answer starts) := by
  exact contextFilteredSplicedSigningOracle_zero_start_update hash enc K
    (completeChainContext hash) pp selector guess answer starts x hzero hn hepoch hchain
/-- The zero-cut filtered winning mass is independent of the old selected start. -/
private theorem runContextFilteredSpliced_zero_start_update_mass
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (observe : GXMSS.PublicKey PP H → (Epoch h → Fin v → H) →
      SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v) →
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v) → Bool)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    𝒟[(fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))]
      {true} =
    𝒟[(fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector guess answer starts] {true} := by
  have hend := splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn
  have hhandler := contextFilteredSplicedSigningOracle_zero_start_update
    hash enc K ctx pp selector guess answer starts x hzero hn hepoch hchain
  rw [hend] at hhandler
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
  unfold runContextFilteredSpliced
  dsimp only
  rw [hend, hhandler]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  apply bind_congr
  intro z
  cases z with
  | mk forgery state =>
    cases state <;> rfl
private theorem runFilteredSpliced_zero_start_update_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))]
      {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer starts] {true} := by
  have hend := splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn
  have hhandler := filteredSplicedSigningOracle_zero_start_update
    hash enc K pp selector guess answer starts x hzero hn hepoch hchain
  rw [hend] at hhandler
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
  unfold runFilteredSpliced
  dsimp only
  rw [hend, hhandler]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  apply bind_congr
  intro z
  cases z with
  | mk forgery state =>
    cases state <;> rfl

/-- At a fixed seed and selector, a real first-step challenge can be sampled independently of
the otherwise unused old selected start, without changing returned selected winning mass. -/
private theorem context_filteredZero_real_source_mass
    [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v)
    (observe : GXMSS.PublicKey PP H → (Epoch h → Fin v → H) →
      SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v) →
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v) → Bool)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice)
        0 1 (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
      return out.elim false
        (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
      return out.elim false
        (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)] {true} := by
  classical
  let : MeasurableSpace H := ⊤
  let F : H → (Epoch h → Fin v → H) → ProbComp Bool := fun answer starts =>
    (fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
  have hpoint (x : H) (starts : Epoch h → Fin v → H) :
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} =
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
    simp only [Function.update_self]
    exact runContextFilteredSpliced_zero_start_update_mass hash enc K ctx adv pp selector splice
      (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x)
      starts x observe hzero hn hepoch hchain
  have hresample := sampleStarts_coordinate_resampling_bind
    (H := H) (α := Bool) (guessedEpoch splice) (guessedChain splice)
    (fun starts => F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
      (starts (guessedEpoch splice) (guessedChain splice))) starts)
  change 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
    GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))] =
    𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] at hresample
  have hcouple : 𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] {true} =
    𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
      {true} := by
   calc
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
          ((Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
            (guessedEpoch splice) (guessedChain splice)))
          (Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} := congrArg (· {true}) hresample.symm
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro x
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro starts
      exact hpoint x starts
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple
private theorem filteredZero_real_source_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice)
        0 1 (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} := by
  classical
  let : MeasurableSpace H := ⊤
  let F : H → (Epoch h → Fin v → H) → ProbComp Bool := fun answer starts =>
    (fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts
  have hpoint (x : H) (starts : Epoch h → Fin v → H) :
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} =
      𝒟[F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
    simp only [Function.update_self]
    exact runFilteredSpliced_zero_start_update_mass hash enc K adv pp selector splice
      (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x)
      starts x hzero hn hepoch hchain
  have hresample := sampleStarts_coordinate_resampling_bind
    (H := H) (α := Bool) (guessedEpoch splice) (guessedChain splice)
    (fun starts => F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
      (starts (guessedEpoch splice) (guessedChain splice))) starts)
  change 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
    GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        ((Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
          (guessedEpoch splice) (guessedChain splice)))
        (Function.update starts (guessedEpoch splice)
          (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))] =
    𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] at hresample
  have hcouple : 𝒟[GXMSS.sampleStarts H h v >>= fun starts =>
      F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))) starts] {true} =
    𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
      {true} := by
   calc
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
          ((Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))
            (guessedEpoch splice) (guessedChain splice)))
          (Function.update starts (guessedEpoch splice)
            (Function.update (starts (guessedEpoch splice)) (guessedChain splice) x))]
        {true} := congrArg (· {true}) hresample.symm
    _ = 𝒟[($ᵗ H : ProbComp H) >>= fun x =>
      GXMSS.sampleStarts H h v >>= fun starts =>
        F (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x) starts]
        {true} := by
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro x
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro starts
      exact hpoint x starts
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple
/-- Advancing the filtered honest response from the first positive step to the selected cut
preserves the full adaptive filtered computation, including its absorbing abort state. -/
private theorem runContextFilteredSpliced_honest_from_zero
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector : Guess h w v) (starts : Epoch h → Fin v → H)
    (hn : 0 < 2 ^ w - 1) :
    runContextFilteredSpliced hash enc K ctx adv pp selector
      (guessedEpoch selector, guessedChain selector, ⟨0, hn⟩)
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0 1
        (starts (guessedEpoch selector) (guessedChain selector))) starts =
    runContextFilteredSpliced hash enc K ctx adv pp selector selector
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0
        ((guessedPosition selector).val + 1)
        (starts (guessedEpoch selector) (guessedChain selector))) starts := by
  let g := (guessedPosition selector).val
  let ep := guessedEpoch selector
  let i := guessedChain selector
  let start := starts ep i
  let splice (j : ℕ) (hj : j ≤ g) : Guess h w v :=
    (ep, i, ⟨j, lt_of_le_of_lt hj (guessedPosition selector).isLt⟩)
  have hiter : ∀ j (hj : j ≤ g),
      runContextFilteredSpliced hash enc K ctx adv pp selector (splice 0 (by omega))
        (hash.chain pp ep i 0 1 start) starts =
      runContextFilteredSpliced hash enc K ctx adv pp selector (splice j hj)
        (hash.chain pp ep i 0 (j + 1) start) starts := by
    intro j
    induction j with
    | zero =>
      intro hj
      rfl
    | succ j ih =>
      intro hj
      have hjprev : j ≤ g := by omega
      have hnext := runContextFilteredSpliced_advance hash enc K ctx adv pp selector
        (splice j hjprev) (splice (j + 1) hj)
        (hash.chain pp ep i 0 (j + 1) start) starts
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by change (⟨j + 1, _⟩ : Fin (2 ^ w - 1)) ≤ guessedPosition selector
            exact Fin.le_iff_val_le_val.mpr hj)
      have hchain : hash.chain pp ep i (j + 1) 1
          (hash.chain pp ep i 0 (j + 1) start) =
          hash.chain pp ep i 0 (j + 1 + 1) start := by
        simpa only [Nat.zero_add] using
          (hash.chain_add pp ep i 0 (j + 1) 1 start).symm
      simp only [splice, guessedEpoch, guessedChain, guessedPosition] at hnext
      rw [hchain] at hnext
      simpa only [Nat.succ_eq_add_one] using (ih hjprev).trans hnext
  have hzero : splice 0 (by omega) =
      (ep, i, (⟨0, hn⟩ : Fin (2 ^ w - 1))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  have hfinal : splice g (Nat.le_refl g) = selector := by
    rcases selector with ⟨⟨ep', i'⟩, pos⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
  simpa only [hzero, hfinal, ep, i, g, start] using hiter g (Nat.le_refl g)
/-- At an honest cut response, the full adaptive spliced interaction is the source interaction
with the same fixed keys and exactly the same optional signing law. -/
private theorem runSpliced_honest
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    runSpliced hash enc K adv pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      runWithKeys hash enc K adv
        (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 := by
  unfold runSpliced runWithKeys
  rw [show splicedEndpoints hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      GXMSS.endpoints hash pp starts from
        splicedEndpoints_honest hash pp guess starts]
  simp only [GXMSS.keys]
  rw [splicedSigningOracle_honest hash enc K pp guess starts]

/-- The complete filtered interaction specializes the deterministic context advance law. -/
private theorem runFilteredSpliced_honest_from_zero
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector : Guess h w v) (starts : Epoch h → Fin v → H)
    (hn : 0 < 2 ^ w - 1) :
    runFilteredSpliced hash enc K adv pp selector
      (guessedEpoch selector, guessedChain selector, ⟨0, hn⟩)
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0 1
        (starts (guessedEpoch selector) (guessedChain selector))) starts =
    runFilteredSpliced hash enc K adv pp selector selector
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0
        ((guessedPosition selector).val + 1)
        (starts (guessedEpoch selector) (guessedChain selector))) starts := by
  exact runContextFilteredSpliced_honest_from_zero hash enc K (completeChainContext hash)
    adv pp selector starts hn

private def jointHonestSpliceProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runSpliced hash enc K adv pp guess answer starts
  return jointChainObservation hash enc K (guess, out)
private theorem jointHonestSpliceProgram_eq_source
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointHonestSpliceProgram hash enc K adv =
      jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv := by
  unfold jointHonestSpliceProgram gameFive sourceProgram GXMSS.keygen
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro guess
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [runSpliced_honest hash enc K adv pp guess starts]
private def jointFilteredHonestProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private def jointZeroRealProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let x ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private def jointZeroRealNormalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private theorem jointZeroRealProgram_eq_normalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram hash enc K adv] =
      𝒟[jointZeroRealNormalized hash enc K adv] := by
  unfold jointZeroRealProgram jointZeroRealNormalized
  rw [OracleComp.evalDist_bind_bind_swap
    ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) hash.thf.seedGen]
  apply evalDist_bind_congr
  intro pp
  apply evalDist_bind_congr
  intro guess
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ H : ProbComp H)
    (GXMSS.sampleStarts H h v) _
/-- Filtering preserves the unconditioned selected source mass after all outer draws. -/
private theorem jointHonestSplice_mass_eq_filtered
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointHonestSpliceProgram hash enc K adv] {true} =
      𝒟[jointFilteredHonestProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointHonestSpliceProgram jointFilteredHonestProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    runSpliced_selectedMass_eq_filtered hash enc K adv pp guess guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts
/-- The filtered source mass equals the independently sampled real zero-cut hybrid. -/
private theorem jointFilteredHonest_mass_eq_zeroReal
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointFilteredHonestProgram hash enc K adv] {true} =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))
  unfold jointFilteredHonestProgram jointZeroRealProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess, ⟨0, hn⟩)
  have hcut : 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} =
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} := by
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro starts
    dsimp only
    rw [← runFilteredSpliced_honest_from_zero hash enc K adv pp guess starts hn]
  rw [hcut]
  simpa only [zero, guessedEpoch, guessedChain] using
    filteredZero_real_source_mass hash enc K adv pp guess zero rfl hn rfl rfl
/-- The exact source selected mass is the returned true mass of the real zero-cut hybrid. -/
private theorem jointChainAdvantage_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  unfold jointChainAdvantage jointChainOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist,
    ← jointHonestSpliceProgram_eq_source hash enc K hv hw adv]
  exact (jointHonestSplice_mass_eq_filtered hash enc K adv).trans
    (jointFilteredHonest_mass_eq_zeroReal hash enc K adv)
/-- A cancellation-free finite telescope suitable for subprobability event masses. -/
private theorem finite_chain_hybrid_telescope (f : ℕ → ℝ≥0∞) (n : ℕ) :
    f 0 + ∑ j ∈ Finset.range n, f (j + 1) =
      f n + ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    ac_rfl
/-- A finite additive telescope yields the desired loss from one Boolean UD distance. -/
private theorem finite_hybrid_boolDist_bound
    (source terminal real ideal distance : ℝ≥0∞) (n : ℕ)
    (hfinite : (n : ℝ≥0∞) * ideal ≠ ∞)
    (htelescope : source + (n : ℝ≥0∞) * ideal =
      terminal + (n : ℝ≥0∞) * real)
    (hdistance : real ≤ ideal + distance) :
    source ≤ terminal + (n : ℝ≥0∞) * distance := by
  apply ENNReal.le_of_add_le_add_right hfinite
  calc
    source + (n : ℝ≥0∞) * ideal =
        terminal + (n : ℝ≥0∞) * real := htelescope
    _ ≤ terminal + (n : ℝ≥0∞) * (ideal + distance) := by
      gcongr
    _ = (terminal + (n : ℝ≥0∞) * distance) +
        (n : ℝ≥0∞) * ideal := by
      rw [mul_add]
      ac_rfl
/-- A uniform finite hybrid index averages unconditioned returned true masses. -/
private theorem uniform_fin_bind_true_mass (n : ℕ) [NeZero n]
    (f : Fin n → ProbComp Bool) :
    𝒟[($ᵗ (Fin n) : ProbComp (Fin n)) >>= f] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j : Fin n, 𝒟[f j] {true} := by
  rw [evalDist_bind_of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn_univ_bind_apply (fun j => 𝒟[f j]) {true}
      (measurableSet_singleton true)]
  simp only [Fintype.card_fin, Finset.mul_sum]
/-- Zeroing all hybrid indices beyond a selected cut leaves its finite prefix sum. -/
private theorem fin_sum_lt_eq_range (n g : ℕ) (hg : g ≤ n)
    (f : ℕ → ℝ≥0∞) :
    (∑ j : Fin n, if j.val < g then f j.val else 0) =
      ∑ j ∈ Finset.range g, f j := by
  change (∑ j : Fin n, (fun k : ℕ => if k < g then f k else 0) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < g then f k else 0) n]
  have hsum := Finset.sum_range_add_sum_Ico
    (fun j : ℕ => if j < g then f j else 0) hg
  rw [← hsum]
  have hprefix : (∑ j ∈ Finset.range g, if j < g then f j else 0) =
      ∑ j ∈ Finset.range g, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have htail : (∑ j ∈ Finset.Ico g n, if j < g then f j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]
  rw [hprefix, htail, add_zero]
/-- Pointwise selected-cut masses average to the exact finite-prefix sum. -/
private theorem uniform_fin_prefix_true_mass_of_pointwise
    (n g : ℕ) [NeZero n] (hg : g ≤ n)
    (actual : Fin n → ProbComp Bool) (f : ℕ → ℝ≥0∞)
    (hpoint : ∀ j : Fin n,
      𝒟[actual j] {true} = if j.val < g then f j.val else 0) :
    𝒟[do let j ← ($ᵗ (Fin n) : ProbComp (Fin n)); actual j] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, f j := by
  rw [uniform_fin_bind_true_mass]
  simp_rw [hpoint]
  exact congrArg ((n : ℝ≥0∞)⁻¹ * ·) (fin_sum_lt_eq_range n g hg f)
private theorem finite_chain_hybrid_mean_telescope (real ideal : ℕ → ℝ≥0∞)
    (n g : ℕ) [NeZero n]
    (htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j) :
    real 0 + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, ideal j) =
    real g + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, real j) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  have hntop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, one_mul] using htelescope

end GXMSS.Reductions

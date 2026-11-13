/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import all HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import HashSig.GXMSS.Security.Interval.Auxiliary.Interaction
import VCVio.CryptoFoundations.SyncSignatureAlg
import VCVio.EvalDist.Monad.UniformTable
import VCVio.OracleComp.EvalDist.Sum

/-!
# Selected interval source mass and finite adaptive telescopes

Uniform coordinate resampling and absorbing history filters preserve the returned selected event.
The source experiment samples the actual public seed and retains one filler table and all history
sources. No conditional normalization or missing-mass equality is assumed.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

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
  · simp only [runContextSpliced, runWithSigningKernel, oraclesWithSigningKernel,
      contextSplicedSigningOracle, raw, event, original, endpoints, pk, sk,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · simp only [runContextFilteredSpliced, rawFiltered, event, filtered, endpoints,
      pk, sk, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro x
    cases x.2 <;> rfl

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
      apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
      intro x _
      apply evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton true)
      intro starts _
      exact hpoint x starts
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple

/-- Advancing the filtered honest response from the first positive step to the selected cut
preserves the full adaptive filtered computation, including its absorbing killed state. -/
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

/-- For one seed and one selector, the filtered ideal cut advances to the next real cut.
The resulting finite telescope concerns returned true mass only. -/
private theorem context_fixed_selector_filtered_hybrid_telescope
    [SampleableType H] [SampleableType R]
    [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (selector : Guess h w v)
    (observe : Result PP H M R h v → Bool) :
    let ep := guessedEpoch selector
    let i := guessedChain selector
    let g := (guessedPosition selector).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat (2 ^ w - 1) j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => observe result)
    let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector (cut j)
        (hash.chain pp ep i j 1 x) starts
      return event out] {true}
    let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector (cut j) x starts
      return event out] {true}
    real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
  let ep := guessedEpoch selector
  let i := guessedChain selector
  let g := (guessedPosition selector).val
  let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat (2 ^ w - 1) j)
  let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
    (fun result => observe result)
  let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runContextFilteredSpliced hash enc K ctx adv pp selector (cut j)
      (hash.chain pp ep i j 1 x) starts
    return event out] {true}
  let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runContextFilteredSpliced hash enc K ctx adv pp selector (cut j) x starts
    return event out] {true}
  change real 0 + ∑ j ∈ Finset.range g, ideal j =
    real g + ∑ j ∈ Finset.range g, real j
  have hnext (j : ℕ) (hj : j < g) : ideal j = real (j + 1) := by
    have hjlt : j < 2 ^ w - 1 := by
      have := (guessedPosition selector).isLt
      omega
    have hj1lt : j + 1 < 2 ^ w - 1 := by
      have := (guessedPosition selector).isLt
      omega
    have hcutj : (guessedPosition (cut j)).val = j := by
      simp [cut, guessedPosition, Nat.mod_eq_of_lt hjlt]
    have hcutj1 : (guessedPosition (cut (j + 1))).val = j + 1 := by
      simp [cut, guessedPosition, Nat.mod_eq_of_lt hj1lt]
    have hstep (starts : Epoch h → Fin v → H) (x : H) :
        runContextFilteredSpliced hash enc K ctx adv pp selector (cut j) x starts =
        runContextFilteredSpliced hash enc K ctx adv pp selector (cut (j + 1))
          (hash.chain pp ep i (j + 1) 1 x) starts := by
      have h := runContextFilteredSpliced_advance hash enc K ctx adv pp selector
        (cut j) (cut (j + 1)) x starts
        (by rfl) (by rfl) (by omega) (by rfl) (by rfl)
        (by apply Fin.le_iff_val_le_val.mpr; simpa only [hcutj1, g] using Nat.succ_le_iff.mpr hj)
      simpa only [cut, guessedEpoch, guessedChain, hcutj] using h
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro starts
    apply bind_congr
    intro x
    simp only [event]
    rw [hstep starts x]
  have hsum : (∑ j ∈ Finset.range g, ideal j) =
      ∑ j ∈ Finset.range g, real (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hnext j (Finset.mem_range.mp hj)
  rw [hsum]
  calc
    _ = ∑ j ∈ Finset.range (g + 1), real j := by
      rw [Finset.sum_range_succ', add_comm]
    _ = _ := Finset.sum_range_succ_comm real g

/-- A returned spliced execution retains the supplied seed and all spliced endpoints. -/
private theorem runContextSpliced_support_keys [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced hash enc K ctx adv pp guess answer starts)) :
    out.pk.seed = pp ∧ out.sk.endpoints =
      splicedEndpoints hash pp guess answer starts := by
  simp only [runContextSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact ⟨rfl, rfl⟩

private theorem context_fixed_selector_returned_measure_telescope
    [SampleableType H] [SampleableType R]
    [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (observe : Result PP H M R h v → Bool) :
    let n := 2 ^ w - 1
    let ep := guessedEpoch guess
    let i := guessedChain guess
    let g := (guessedPosition guess).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat n j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => observe result)
    let source : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut 0)
        (hash.chain pp ep i 0 1 x) starts
      return event out
    let terminal : ProbComp Bool := do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runContextFilteredSpliced hash enc K ctx adv pp guess guess
        (hash.chain pp ep i g 1 x) starts
      return event out
    let selected : SM_DT_UD_World → ProbComp Bool := fun world => do
      let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let answer := match world with
        | .real => hash.chain pp ep i j.val 1 x
        | .ideal => x
      if j.val < g then
        let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut j.val) answer starts
        return event out
      else return false
    𝒟[source] {true} + (n : ℝ≥0∞) * 𝒟[selected .ideal] {true} =
      𝒟[terminal] {true} + (n : ℝ≥0∞) * 𝒟[selected .real] {true} := by
  let n := 2 ^ w - 1
  let ep := guessedEpoch guess
  let i := guessedChain guess
  let g := (guessedPosition guess).val
  let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat n j)
  let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
    (fun result => observe result)
  let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut j)
      (hash.chain pp ep i j 1 x) starts
    return event out] {true}
  let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
    let starts ← GXMSS.sampleStarts H h v
    let x ← ($ᵗ H : ProbComp H)
    let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut j) x starts
    return event out] {true}
  have htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
    simpa only [real, ideal, n, ep, i, g, cut, event] using
      context_fixed_selector_filtered_hybrid_telescope hash enc K ctx adv pp guess observe
  have hg : g ≤ n := by
    have := (guessedPosition guess).isLt
    omega
  have hcutg : cut g = guess := by
    rcases guess with ⟨epoch, chain, position⟩
    change (epoch, chain, Fin.ofNat n position.val) = (epoch, chain, position)
    simp only [Prod.mk.injEq, true_and]
    apply Fin.ext
    change position.val % (2 ^ w - 1) = position.val
    exact Nat.mod_eq_of_lt position.isLt
  have haverage (actual : Fin n → ProbComp Bool) (f : ℕ → ℝ≥0∞)
      (hpoint : ∀ j : Fin n, 𝒟[actual j] {true} = if j.val < g then f j.val else 0) :
      𝒟[do let j ← ($ᵗ (Fin n) : ProbComp (Fin n)); actual j] {true} =
        (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, f j := by
    rw [evalDist_bind_of_discrete, SampleableType.evalDist_uniformSample,
      ProbabilityTheory.uniformOn_univ_bind_apply (fun j => 𝒟[actual j]) {true}
        (measurableSet_singleton true)]
    simp only [Fintype.card_fin, ← Finset.mul_sum]
    simp_rw [hpoint]
    apply congrArg ((n : ℝ≥0∞)⁻¹ * ·)
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
  have hideal :
      𝒟[do
        let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        if j.val < g then
          let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut j.val) x starts
          return event out
        else return false] {true} =
        (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, ideal j := by
    apply haverage _ ideal
    intro j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceIte, ideal]
    · simp only [hj, ↓reduceIte]
      simp only [OracleComp.evalDist_bind_const, evalDist_pure]
      simp
  have hreal :
      𝒟[do
        let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        if j.val < g then
          let out ← runContextFilteredSpliced hash enc K ctx adv pp guess (cut j.val)
            (hash.chain pp ep i j.val 1 x) starts
          return event out
        else return false] {true} =
        (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, real j := by
    apply haverage _ real
    intro j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceIte, real]
    · simp only [hj, ↓reduceIte]
      simp only [OracleComp.evalDist_bind_const, evalDist_pure]
      simp
  change real 0 + (n : ℝ≥0∞) * _ = _ + (n : ℝ≥0∞) * _
  rw [hideal, hreal]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp only [← mul_assoc, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  simpa only [real, ep, i, g, event, hcutg] using htelescope

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability
  GXMSS.Reductions GXMSS.IntervalMerkle
variable {PP T X H M R : Type} {h w v : ℕ}

/-- The actual selected active event uses the mixed path and discharges the filtering premise. -/
private theorem intervalSelectedSplice_mass_eq_filtered
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (selector splice : Guess h w v) (response : H) (starts : Epoch h → Fin v → H) :
    𝒟[intervalSelectedChainObservation P enc K I fillers selector <$>
      runContextSpliced P enc K (intervalChainContext P I fillers) A pp splice response starts]
        {true} =
    𝒟[(fun out => out.elim false
      (intervalSelectedChainObservation P enc K I fillers selector)) <$>
      runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp
        selector splice response starts] {true} := by
  exact runContextSpliced_selectedMass_eq_filtered P enc K (intervalChainContext P I fillers)
    A pp selector splice response starts
    (intervalSelectedChainObservation P enc K I fillers selector)
    (intervalSelectedChainObservation_not_bad P enc K I fillers selector)

private theorem intervalSelectedSplice_zero_real_resampling
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (selector splice : Guess h w v)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let response := P.chain pp (guessedEpoch splice) (guessedChain splice) 0 1
        (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp
        selector splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers selector))]
        {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let response := P.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp
        selector splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers selector))]
        {true} := by
  exact context_filteredZero_real_source_mass P enc K (intervalChainContext P I fillers)
    A pp selector splice
    (fun pk endpoints forgery history => intervalSelectedChainObservation P enc K I fillers
      selector ⟨pk, ⟨pk.seed, endpoints, endpoints⟩, forgery, history⟩)
    hzero hn hepoch hchain

private theorem runContextSpliced_honest_interval
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    runContextSpliced P enc K (intervalChainContext P I fillers) A pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts = (do
        let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
        let view ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
        let (publicKey, forgery, history) := view
        pure (⟨publicKey, sk.complete, forgery, history⟩ : Result PP H M R h v)) := by
  have hend := splicedEndpoints_honest P pp guess starts
  have hkernel := intervalSplicedSign_honest P enc K I pp guess starts fillers
  dsimp only [intervalSplicedSign] at hkernel
  unfold runContextSpliced
  rw [hend]
  dsimp only
  rw [hkernel]
  simp only [intervalChainContext, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.Interval.viewWithKeys, bind_assoc]
  rfl

end GXMSS.Interval.Reductions

namespace GXMSS.Interval.Reductions.Chain
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability
  GXMSS.Reductions GXMSS.IntervalMerkle
variable {PP T X H M R : Type} {h w v : ℕ}

private noncomputable def jointOuterDraw
    [SampleableType H] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v) (I : Interval h) :
    ProbComp (PP × Guess h w v × Fillers I H) := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let fillers ← sampleFillers I H
    pure (pp, activeGuess I selector, fillers)

private noncomputable def fixedSelectedSourceProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (fillers : Fillers I H) : ProbComp Bool := do
  let starts ← GXMSS.sampleStarts H h v
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  let view ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  let (publicKey, forgery, history) := view
  pure (intervalSelectedChainObservation P enc K I fillers guess
    ⟨publicKey, sk.complete, forgery, history⟩)

/-- Select an active epoch/chain/position independently of the actual interval signing view.
The event retains active matching, the encoding/chain filters and all three history sources. -/
noncomputable def selectedSourceExperiment
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact do
    let (pp, guess, fillers) ← jointOuterDraw P I
    fixedSelectedSourceProgram P enc K I A pp guess fillers

end GXMSS.Interval.Reductions.Chain

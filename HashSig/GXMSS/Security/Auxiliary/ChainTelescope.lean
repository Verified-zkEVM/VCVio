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
public import HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
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
# Selected chain mass and context telescopes

Exact selected-mass accounting and context-indexed finite telescopes retain successful, unused
and failed-consumed epochs. All comparisons use native returned measures, including false
outcomes and missing mass.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- The enlarged single selector exactly accounts for all returned Game 4 wins, including
unused and failed-consumed forged epochs. Returned false and missing mass stay unconditioned. -/
theorem jointChainAdvantage_eq_gameFourAdvantage_div_guess_card
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc) :
    jointChainAdvantage hash enc K hv hw adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ *
        gameFourAdvantage hash enc K adv := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  let source := sourceProgram hash enc K adv
  let c : ℝ≥0∞ := (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹
  have hmass : gameFourAdvantage hash enc K adv =
      𝒟[source] {out | gameFourObservation hash enc K out = true} := by
    simp only [gameFourAdvantage, gameFourOutputMeasure, gameFour,
      ProbCompRuntime.probComp_evalDist]
    rw [evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hswap :
      𝒟[jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv] =
        𝒟[do
          let out ← source
          let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
          return jointChainObservation hash enc K (guess, out)] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  have hconditional : ∀ out ∈ support source,
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return jointChainObservation hash enc K (guess, out)] {true} =
        if gameFourObservation hash enc K out = true then c else 0 := by
    intro out hout
    have hprob := jointChainGuess_probability hash enc K adv hnonmax out hout
    have hobs : Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
        jointChainObservation hash enc K (guess, out) = true] =
        𝒟[(fun guess => jointChainObservation hash enc K (guess, out)) <$>
          ($ᵗ (Guess h w v) : ProbComp (Guess h w v))] {true} := by
      exact (prEvent_map _ (fun guess => jointChainObservation hash enc K (guess, out))
        (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  have hae : ∀ᵐ out ∂𝒟[source],
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return jointChainObservation hash enc K (guess, out)] {true} =
        if gameFourObservation hash enc K out = true then c else 0 :=
    evalDist.ae_of_forall_mem_support source _ MeasurableSet.of_discrete hconditional
  unfold jointChainAdvantage jointChainOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist, hswap, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_congr_ae hae]
  have hfun : (fun out : Result PP H M R h v =>
      if gameFourObservation hash enc K out = true then c else 0) =
      ({out | gameFourObservation hash enc K out = true} : Set _).indicator
        (fun _ => c) := by
    funext out
    by_cases h : gameFourObservation hash enc K out = true <;> simp [h]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
    ← hmass]
/-- Exact finite-selector accounting for all returned Game 4 winning mass. -/
theorem gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc) :
    gameFourAdvantage hash enc K adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        jointChainAdvantage hash enc K hv hw adv := by
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
  rw [jointChainAdvantage_eq_gameFourAdvantage_div_guess_card
    hash enc K hv hw adv hnonmax, ENNReal.mul_inv_cancel_left hne htop]
/-- The native returned-measure Game 4→5 bound before either non-success mass has been charged.
The two residual terms retain unused-query and failed-consumed outcomes separately. -/
theorem gameFourAdvantage_le_gameFive_add_unpaid_masses
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFourAdvantage hash enc K adv ≤
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        gameFiveAdvantage hash enc K hv hw adv +
          unusedGameFourMass hash enc K adv +
            failedConsumedGameFourMass hash enc K adv := by
  calc
    gameFourAdvantage hash enc K adv ≤
        successfulGameFourMass hash enc K adv +
          nonSuccessGameFourMass hash enc K adv :=
      gameFourAdvantage_le_successful_add_nonSuccess hash enc K adv
    _ ≤ successfulGameFourMass hash enc K adv +
        (unusedGameFourMass hash enc K adv +
          failedConsumedGameFourMass hash enc K adv) := by
      gcongr
      exact nonSuccessGameFourMass_le_unused_add_failedConsumed hash enc K adv
    _ = _ := by
      rw [successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
        hash enc K hv hw adv]
      ac_rfl
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
  exact finite_chain_hybrid_telescope real g
private theorem fixed_selector_filtered_hybrid_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (selector : Guess h w v) :
    let ep := guessedEpoch selector
    let i := guessedChain selector
    let g := (guessedPosition selector).val
    let cut : ℕ → Guess h w v := fun j => (ep, i, Fin.ofNat (2 ^ w - 1) j)
    let event : Option (Result PP H M R h v) → Bool := fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))
    let real : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp selector (cut j)
        (hash.chain pp ep i j 1 x) starts
      return event out] {true}
    let ideal : ℕ → ℝ≥0∞ := fun j => 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let x ← ($ᵗ H : ProbComp H)
      let out ← runFilteredSpliced hash enc K adv pp selector (cut j) x starts
      return event out] {true}
    real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
  exact context_fixed_selector_filtered_hybrid_telescope hash enc K (completeChainContext hash)
    adv pp selector (fun result => jointChainObservation hash enc K (selector, result))

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
/-- A successful record in a returned spliced run is exactly the signature made from its
successful retry codeword. -/
private theorem runContextSpliced_successful_record_signature
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced hash enc K ctx adv pp guess answer starts))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = contextSplicedSignatureOfWord hash ctx pp guess answer starts
        (splicedEndpoints hash pp guess answer starts) ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  let endpoints := splicedEndpoints hash pp guess answer starts
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      contextSplicedSigningOracle hash enc K ctx pp guess answer starts endpoints
  have hpres : QueryImpl.PreservesInv impl
      (contextSplicedSuccessfulHistoryEncodes hash enc ctx pp guess answer starts endpoints) := by
    intro q history hinv z hz
    cases q with
    | inl uniform =>
      simp only [impl, QueryImpl.add_apply_inl] at hz
      simp only [QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, history)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      exact hinv
    | inr signing =>
      simpa only [impl, QueryImpl.add_apply_inr] using
        (contextSplicedSigningOracle_preserves_successfulHistoryEncodes hash enc K ctx pp guess
          answer starts endpoints signing history hinv z hz)
  have hinit : contextSplicedSuccessfulHistoryEncodes hash enc ctx pp guess answer starts
      endpoints SyncSignatureUnforgeability.emptyHistory := by
    intro ep msg sig hentry
    simp [SyncSignatureUnforgeability.emptyHistory] at hentry
  simp only [runContextSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  have hfinal := OracleComp.simulateQ_run_preservesInv impl
    (contextSplicedSuccessfulHistoryEncodes hash enc ctx pp guess answer starts endpoints)
      hpres (adv.forge ⟨ctx.root pp endpoints, pp⟩)
      SyncSignatureUnforgeability.emptyHistory hinit pair
  exact hfinal (by simpa only [impl, endpoints] using hpair) ep msg sig hrecord
private theorem runSpliced_support_keys [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts)) :
    out.pk.seed = pp ∧ out.sk.endpoints =
      splicedEndpoints hash pp guess answer starts := by
  simp only [runSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact ⟨rfl, rfl⟩
/-- A successful record in a returned spliced run is exactly the signature made from its
successful retry codeword. -/
private theorem runSpliced_successful_record_signature
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runSpliced hash enc K adv pp guess answer starts))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = splicedSignatureOfWord hash pp guess answer starts
        (splicedEndpoints hash pp guess answer starts) ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  let endpoints := splicedEndpoints hash pp guess answer starts
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      splicedSigningOracle hash enc K pp guess answer starts endpoints
  have hpres : QueryImpl.PreservesInv impl
      (splicedSuccessfulHistoryEncodes hash enc pp guess answer starts endpoints) := by
    intro q history hinv z hz
    cases q with
    | inl uniform =>
      simp only [impl, QueryImpl.add_apply_inl] at hz
      simp only [QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, history)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      exact hinv
    | inr signing =>
      simpa only [impl, QueryImpl.add_apply_inr] using
        (splicedSigningOracle_preserves_successfulHistoryEncodes hash enc K pp guess
          answer starts endpoints signing history hinv z hz)
  have hinit : splicedSuccessfulHistoryEncodes hash enc pp guess answer starts
      endpoints SyncSignatureUnforgeability.emptyHistory := by
    intro ep msg sig hentry
    simp [SyncSignatureUnforgeability.emptyHistory] at hentry
  simp only [runSpliced, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  have hfinal := OracleComp.simulateQ_run_preservesInv impl
    (splicedSuccessfulHistoryEncodes hash enc pp guess answer starts endpoints)
      hpres (adv.forge ⟨hash.merkleRoot pp endpoints, pp⟩)
      SyncSignatureUnforgeability.emptyHistory hinit pair
  exact hfinal (by simpa only [impl, endpoints] using hpair) ep msg sig hrecord

private theorem bind_true_mass_telescope {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (draw : ProbComp α)
    (source ideal terminal real : α → ProbComp Bool) (n : ℕ)
    (h : ∀ a,
      𝒟[source a] {true} + (n : ℝ≥0∞) * 𝒟[ideal a] {true} =
        𝒟[terminal a] {true} + (n : ℝ≥0∞) * 𝒟[real a] {true}) :
    𝒟[draw >>= source] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= ideal] {true} =
      𝒟[draw >>= terminal] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= real] {true} := by
  simp only [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[ideal a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[source a] {true})]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[real a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[terminal a] {true})]
  exact MeasureTheory.lintegral_congr fun a => h a
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
    apply uniform_fin_prefix_true_mass_of_pointwise n g hg _ ideal
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
    apply uniform_fin_prefix_true_mass_of_pointwise n g hg _ real
    intro j
    by_cases hj : j.val < g
    · simp only [hj, ↓reduceIte, real]
    · simp only [hj, ↓reduceIte]
      simp only [OracleComp.evalDist_bind_const, evalDist_pure]
      simp
  change real 0 + (n : ℝ≥0∞) * _ = _ + (n : ℝ≥0∞) * _
  rw [hideal, hreal]
  convert finite_chain_hybrid_mean_telescope real ideal n g htelescope using 1
  simp only [real, ep, i, g, event, hcutg]

end GXMSS.Reductions

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Reductions.CollisionBounds
import all HashSig.GXMSS.Security.Reductions.CollisionBounds
public import HashSig.GXMSS.Security.Reductions.ReductionExperiments
import all HashSig.GXMSS.Security.Reductions.ReductionExperiments
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSimulation
import all HashSig.GXMSS.Security.Interval.Reductions.ActiveSimulation
public import HashSig.GXMSS.Security.Interval.Reductions.ChainReductions
import all HashSig.GXMSS.Security.Interval.Reductions.ChainReductions
public import HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid
import all HashSig.GXMSS.Security.Interval.Reductions.ChainHybrid
public import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
import all HashSig.GXMSS.Security.Interval.Reductions.SourcePartition

/-!
# Active interval probability bounds

An active epoch is selected through its offset in the inclusive interval. The selector's
singleton probability is integrated against the actual adaptive source, preserving unused,
successful and failed-consumed signing histories and unreturned mass.
-/

public section

namespace GXMSS.Interval.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle Encoding ENNReal
open GXMSS.Reductions GXMSS.Unforgeability GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability

variable {PP T X H M R : Type} {h w v : ℕ}

private def activeOffset (I : Interval h) (epoch : Epoch h) (he : Epoch.IsActive I epoch) :
    Fin ((I.last : ℕ) - (I.first : ℕ) + 1) :=
  ⟨epoch.val - (I.first : ℕ), by
    have ho := I.ordered
    simp only [Epoch.IsActive, Fin.le_iff_val_le_val] at he ho
    omega⟩

private theorem activeGuess_offset (I : Interval h) (epoch : Epoch h)
    (he : Epoch.IsActive I epoch) (chain : Fin v) (position : Fin (2 ^ w - 1)) :
    activeGuess I (activeOffset I epoch he, chain, position) = (epoch, chain, position) := by
  have hlo := he.1
  simp only [Fin.le_iff_val_le_val] at hlo
  apply Prod.ext
  · apply Fin.ext
    simp only [activeGuess, activeOffset]
    omega
  · rfl

private theorem activeGuess_injective (I : Interval h) :
    Function.Injective (activeGuess I : ActiveSelector I w v → Guess h w v) := by
  rintro ⟨offset, chain, position⟩ ⟨offset', chain', position'⟩ heq
  have hepoch := congrArg (fun g : Guess h w v => (guessedEpoch g).val) heq
  have hchain := congrArg guessedChain heq
  have hposition := congrArg guessedPosition heq
  simp only [activeGuess, guessedEpoch, guessedChain, guessedPosition] at hepoch hchain hposition
  have hoffset : offset = offset' := Fin.ext (by omega)
  subst offset'
  subst chain'
  subst position'
  rfl

private theorem selectedCut_singleton_of_active
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (I : Interval h) (out : Result PP H M R h v)
    (he : let forgery := out.forgery; Epoch.IsActive I forgery.1)
    (hex : ∃ target : Guess h w v, intervalSelectedCut enc target out = true) :
    ∃ target : ActiveSelector I w v, ∀ selector : ActiveSelector I w v,
      intervalSelectedCut enc (activeGuess I selector) out = true ↔ selector = target := by
  obtain ⟨guess, hguess⟩ := hex
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at he
  have hunique (i : Fin v) (n : ℕ)
      (hfilter : ∀ g, intervalSelectedCut enc g
        ⟨pk, sk, (epoch, message, signature), history⟩ = true ↔
          guessedEpoch g = epoch ∧ guessedChain g = i ∧
            (guessedPosition g).val + 1 = n) :
      ∃ target : ActiveSelector I w v, ∀ selector : ActiveSelector I w v,
        intervalSelectedCut enc (activeGuess I selector)
          ⟨pk, sk, (epoch, message, signature), history⟩ = true ↔ selector = target := by
    obtain ⟨hgEpoch, hgChain, hgPos⟩ := (hfilter guess).mp hguess
    let pos := guessedPosition guess
    let target : ActiveSelector I w v := (activeOffset I epoch he, i, pos)
    have ht : activeGuess I target = (epoch, i, pos) := activeGuess_offset I epoch he i pos
    refine ⟨target, ?_⟩
    intro selector
    rw [hfilter]
    constructor
    · rintro ⟨hepoch, hchain, hposition⟩
      apply activeGuess_injective I
      rw [ht]
      rcases hg : activeGuess I selector with ⟨ep, ci, pi⟩
      simp only [hg, guessedEpoch, guessedChain, guessedPosition] at hepoch hchain hposition
      have hpos : pi = pos := by
        apply Fin.ext
        change pi.val + 1 = n at hposition
        change pos.val + 1 = n at hgPos
        omega
      exact Prod.ext hepoch (Prod.ext hchain hpos)
    · intro hs
      subst selector
      simp only [ht, guessedEpoch, guessedChain, guessedPosition, true_and]
      exact hgPos
  cases hentry : history epoch with
  | none =>
    cases hword : enc.value pk.seed message signature.randomizer epoch with
    | none => simp [intervalSelectedCut, hentry, hword] at hguess
    | some word =>
      cases hi : findNonMaximumCoordinate word with
      | none => simp [intervalSelectedCut, hentry, hword, hi] at hguess
      | some i => exact hunique i (2 ^ w - 1) (by
          intro g; simp [intervalSelectedCut, hentry, hword, hi])
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
      cases hword : enc.value pk.seed message signature.randomizer epoch with
      | none => simp [intervalSelectedCut, hentry, hword] at hguess
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [intervalSelectedCut, hentry, hword, hi] at hguess
        | some i => exact hunique i (2 ^ w - 1) (by
            intro g; simp [intervalSelectedCut, hentry, hword, hi])
    | some honest =>
      cases hh : enc.value pk.seed first honest.randomizer epoch with
      | none => simp [intervalSelectedCut, hentry, hh] at hguess
      | some honestWord =>
        cases hf : enc.value pk.seed message signature.randomizer epoch with
        | none => simp [intervalSelectedCut, hentry, hh, hf] at hguess
        | some forgedWord =>
          cases hi : GXMSS.Security.findSmallerCoordinate honestWord forgedWord with
          | none => simp [intervalSelectedCut, hentry, hh, hf, hi] at hguess
          | some i => exact hunique i (honestWord i).val (by
              intro g; simp [intervalSelectedCut, hentry, hh, hf, hi])

private theorem remainder_selected_singleton
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hnonmax : NoMaximumOutput enc) (fillers : Fillers I H) (out : Result PP H M R h v)
    (hrem : intervalChainRemainderObservation P enc K I fillers out = true) :
    ∃ target : ActiveSelector I w v, ∀ selector : ActiveSelector I w v,
      intervalSelectedChainObservation P enc K I fillers (activeGuess I selector) out = true ↔
        selector = target := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  have hparts := hrem
  simp only [intervalChainRemainderObservation, Bool.and_eq_true] at hparts
  obtain ⟨⟨⟨hactive, _⟩, _⟩, hcut⟩ := hparts
  cases hw : enc.value pk.seed message signature.randomizer epoch with
  | none => simp [activeMatchingEvent, hw] at hactive
  | some word =>
    have he : Epoch.IsActive I epoch := by
      simp only [activeMatchingEvent, hw, Bool.and_eq_true] at hactive
      exact (of_decide_eq_true hactive.2).1
    have hex : ∃ target : Guess h w v,
        intervalSelectedCut enc target ⟨pk, sk, (epoch, message, signature), history⟩ = true := by
      have hnonSuccess
          (hs : history epoch = none ∨ ∃ first, history epoch = some (first, none)) :
          ∃ target : Guess h w v,
            intervalSelectedCut enc target
              ⟨pk, sk, (epoch, message, signature), history⟩ = true := by
        obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
          (findNonMaximumCoordinate_isSome enc hnonmax _ _ _ _ word hw)
        have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
        let position : Fin (2 ^ w - 1) := ⟨2 ^ w - 2, by omega⟩
        refine ⟨(epoch, i, position), ?_⟩
        rcases hs with hs | ⟨first, hs⟩ <;>
          simp [intervalSelectedCut, hs, hw, hi, guessedEpoch, guessedChain,
            guessedPosition, position, show 2 ^ w - 2 + 1 = 2 ^ w - 1 by omega]
      cases hs : history epoch with
      | none => exact hnonSuccess (Or.inl hs)
      | some entry =>
        rcases entry with ⟨first, answer⟩
        cases answer with
        | none => exact hnonSuccess (Or.inr ⟨first, hs⟩)
        | some honest =>
          have hsource : forgedEpochSource
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) =
              .successful first honest := by simp [forgedEpochSource, hs]
          cases hh : enc.value pk.seed first honest.randomizer epoch with
          | none => simp [designatedCutHolds, hsource, hh] at hcut
          | some honestWord =>
            cases hi : GXMSS.Security.findSmallerCoordinate honestWord word with
            | none => simp [designatedCutHolds, hsource, hh, hw, hi] at hcut
            | some i =>
              have hsmall := GXMSS.Security.findSmallerCoordinate_sound honestWord word hi
              have hpos : 0 < (honestWord i).val := by omega
              let position : Fin (2 ^ w - 1) :=
                ⟨(honestWord i).val - 1, by have := (honestWord i).isLt; omega⟩
              refine ⟨(epoch, i, position), ?_⟩
              simp [intervalSelectedCut, hs, hh, hw, hi, guessedEpoch, guessedChain,
                guessedPosition, position, show (honestWord i).val - 1 + 1 =
                  (honestWord i).val by omega]
    obtain ⟨target, htarget⟩ := selectedCut_singleton_of_active enc I
      ⟨pk, sk, (epoch, message, signature), history⟩ he hex
    exact ⟨target, fun selector => by
      simpa only [intervalSelectedChainObservation, hrem, Bool.true_and] using htarget selector⟩

private theorem activeGuess_probability
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hnonmax : NoMaximumOutput enc) (fillers : Fillers I H) (out : Result PP H M R h v) :
    letI : NeZero ((I.last : ℕ) - (I.first : ℕ) + 1) := ⟨by omega⟩
    Pr{let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))}[
      intervalSelectedChainObservation P enc K I fillers (activeGuess I selector) out = true] =
      if intervalChainRemainderObservation P enc K I fillers out = true then
        (Fintype.card (ActiveSelector I w v) : ℝ≥0∞)⁻¹ else 0 := by
  let : NeZero ((I.last : ℕ) - (I.first : ℕ) + 1) := ⟨by omega⟩
  by_cases hwin : intervalChainRemainderObservation P enc K I fillers out = true
  · obtain ⟨target, htarget⟩ := remainder_selected_singleton P enc K I hnonmax fillers out hwin
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · simp only [hwin]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff _).2
    intro selector hselected
    simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hselected
    exact hwin hselected.1

private noncomputable def activeSource
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp (Fillers I H × Result PP H M R h v) := do
  let pp ← TweakableHash.seedGen P.thf
  let fillers ← sampleFillers I H
  let starts ← GXMSS.sampleStarts H h v
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  let (publicKey, forgery, history) ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (fillers, ⟨publicKey, sk.complete, forgery, history⟩)

private theorem activeRemainder_mass_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[activeRemainderExperiment P enc K I A] {true} =
      𝒟[(fun z => intervalChainRemainderObservation P enc K I z.1 z.2) <$>
        activeSource P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  unfold activeRemainderExperiment activeSource GXMSS.Interval.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
    (evalDist_bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H) _)

private theorem selectedSource_mass_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
    letI : NeZero (2 ^ w - 1) := ⟨by
      have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
    letI : NeZero ((I.last : ℕ) - (I.first : ℕ) + 1) := ⟨by omega⟩
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} =
      𝒟[do
        let (fillers, out) ← activeSource P enc K I A
        let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
        pure (intervalSelectedChainObservation P enc K I fillers (activeGuess I selector) out)]
        {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : NeZero ((I.last : ℕ) - (I.first : ℕ) + 1) := ⟨by omega⟩
  let : MeasurableSpace PP := ⊤
  unfold selectedSourceExperiment jointOuterDraw fixedSelectedSourceProgram activeSource
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  let source : ProbComp (Fillers I H × Result PP H M R h v) := do
    let fillers ← sampleFillers I H
    let starts ← GXMSS.sampleStarts H h v
    let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
    let (publicKey, forgery, history) ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
    pure (fillers, ⟨publicKey, sk.complete, forgery, history⟩)
  have hswap := evalDist_bind_bind_swap
    ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v)) source
    (fun selector z => pure
      (intervalSelectedChainObservation P enc K I z.1 (activeGuess I selector) z.2))
  simp only [source, bind_assoc] at hswap
  refine Eq.trans ?_ (congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hswap)
  congr 1

private theorem selectedSource_mass_eq_inverse_mul_remainder
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (hnonmax : NoMaximumOutput enc)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} =
      ((((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞)⁻¹ *
        𝒟[activeRemainderExperiment P enc K I A] {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : NeZero ((I.last : ℕ) - (I.first : ℕ) + 1) := ⟨by omega⟩
  let : MeasurableSpace (Fillers I H × Result PP H M R h v) := ⊤
  let source := activeSource P enc K I A
  let obs := fun z : Fillers I H × Result PP H M R h v =>
    intervalChainRemainderObservation P enc K I z.1 z.2
  let c : ℝ≥0∞ := (Fintype.card (ActiveSelector I w v) : ℝ≥0∞)⁻¹
  have hconditional (z : Fillers I H × Result PP H M R h v) :
      𝒟[do
        let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
        pure (intervalSelectedChainObservation P enc K I z.1 (activeGuess I selector) z.2)]
        {true} = if obs z = true then c else 0 := by
    have hprob := activeGuess_probability P enc K I hnonmax z.1 z.2
    have hobs : Pr{let selector ←
        ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))}[
        intervalSelectedChainObservation P enc K I z.1 (activeGuess I selector) z.2 = true] =
        𝒟[(fun selector => intervalSelectedChainObservation P enc K I z.1
          (activeGuess I selector) z.2) <$>
          ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))] {true} := by
      exact (prEvent_map _ _ (fun b => b = true)).symm.trans
        (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [obs, c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  rw [selectedSource_mass_eq_source, activeRemainder_mass_eq_source]
  change 𝒟[source >>= _] {true} = _ * 𝒟[obs <$> source] {true}
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  simp_rw [hconditional]
  have hfun : (fun z => if obs z = true then c else 0) =
      ({z | obs z = true} : Set _).indicator (fun _ => c) := by
    funext z
    by_cases hz : obs z = true <;> simp [hz]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
    evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
  simp only [c, activeSelector_card]
  rfl

/-- Exact active-selector accounting for the actual interval remainder. The inclusive epoch
length, chain count and positive chain-position count form the finite factor; no source mass
is conditioned on termination or successful signing. -/
private theorem activeRemainderMass_eq_selectorCount_mul_selectedSourceMass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[activeRemainderExperiment P enc K I A] {true} =
      ((((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        𝒟[selectedSourceExperiment P enc K I hv hw A] {true} := by
  have hn : 0 < 2 ^ w - 1 := by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega
  have hc : 0 < ((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) := by positivity
  have hne : ((((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hc
  -- Cancellation uses the positive inclusive interval length and the two positive digit counts.
  rw [selectedSource_mass_eq_inverse_mul_remainder P enc K I hv hw
    (noMaximumOutput_of_two_codewords enc htwo) A,
    ENNReal.mul_inv_cancel_left hne (ENNReal.natCast_ne_top _)]


private theorem nativeBoolMass_ne_top (program : ProbComp Bool) :
    𝒟[program] {true} ≠ ∞ :=
  ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (evalDist_apply_le_one program {true})

private theorem native_telescope_toReal
    (source ideal terminal real : ProbComp Bool) (n : ℕ)
    (ht : 𝒟[source] {true} + (n : ℝ≥0∞) * 𝒟[ideal] {true} =
      𝒟[terminal] {true} + (n : ℝ≥0∞) * 𝒟[real] {true}) :
    (𝒟[source] {true}).toReal = (𝒟[terminal] {true}).toReal +
      (n : ℝ) * ((𝒟[real] {true}).toReal - (𝒟[ideal] {true}).toReal) := by
  have hprod (p : ProbComp Bool) : (n : ℝ≥0∞) * 𝒟[p] {true} ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (nativeBoolMass_ne_top p)
  have h := congrArg ENNReal.toReal ht
  rw [ENNReal.toReal_add (nativeBoolMass_ne_top source) (hprod ideal),
    ENNReal.toReal_add (nativeBoolMass_ne_top terminal) (hprod real)] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  linarith

private theorem activeRemainderMass_eq_signed_terminal
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) :
    let c : ℝ := (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ)
    (𝒟[activeRemainderExperiment P enc K I A] {true}).toReal =
      c * (𝒟[selectedPreimageExperiment P enc K I hv hw A] {true}).toReal +
        c * (2 ^ w - 1 : ℕ) *
          ((𝒟[SM_DT_UD_Experiment .real
            (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal -
          (𝒟[SM_DT_UD_Experiment .ideal
            (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal) := by
  have ht := native_telescope_toReal _ _ _ _ _
    (selectedSource_native_telescope P enc K I hv hw A)
  rw [activeRemainderMass_eq_selectorCount_mul_selectedSourceMass P enc K I hv hw htwo A,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ht]
  push_cast
  ring

/-- The active matching branch is bounded by its three actual original collision reductions,
the original-domain chain PRE advantage and the signed real-minus-ideal chain UD contribution.
The query bound counts every signing request, including failures, inactive requests and repeats. -/
theorem activeMatchingMass_le_signed_advantages
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    let c : ℝ := (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ)
    (𝒟[activeMatchingExperiment P enc K I A] {true}).toReal ≤
      (TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A)).toReal +
      (SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction
          P enc K I A)).toReal +
      (SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A)).toReal +
      c * (SM_DT_PRE_Advantage (selectedChainPreimageReduction P enc K I hv hw A)).toReal +
      c * (2 ^ w - 1 : ℕ) *
        ((𝒟[SM_DT_UD_Experiment .real
          (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal -
        (𝒟[SM_DT_UD_Experiment .ideal
          (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal) := by
  have hp := activeMatchingMass_le_collision_masses_add_remainder P enc K I hv hw A
  change 𝒟[activeMatchingExperiment P enc K I A] {true} ≤
    𝒟[encodingCollisionExperiment P enc K I A] {true} +
    𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] {true} +
    𝒟[chainCutCollisionExperiment P enc K I A] {true} +
    𝒟[activeRemainderExperiment P enc K I A] {true} at hp
  have hpReal := ENNReal.toReal_mono
    (add_ne_top.mpr ⟨add_ne_top.mpr ⟨add_ne_top.mpr
      ⟨nativeBoolMass_ne_top _, nativeBoolMass_ne_top _⟩, nativeBoolMass_ne_top _⟩,
      nativeBoolMass_ne_top _⟩) hp
  rw [ENNReal.toReal_add (by finiteness) (nativeBoolMass_ne_top _),
    ENNReal.toReal_add (by finiteness) (nativeBoolMass_ne_top _),
    ENNReal.toReal_add (nativeBoolMass_ne_top _) (nativeBoolMass_ne_top _),
    activeRemainderMass_eq_signed_terminal P enc K I hv hw htwo A] at hpReal
  have he := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (encodingCollisionMass_le_advantage P enc qs K I A hqueries)
  have hf := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (sameMessageRandomizerChainCollisionMass_le_advantage P enc K I hv hw A)
  have hs := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (chainCutCollisionMass_le_advantage P enc K I hv hw A)
  have hpre := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (selectedPreimageMass_le_advantage P enc K I hv hw A)
  have hc : (0 : ℝ) ≤ (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) := by positivity
  simp only [ProbCompRuntime.probComp_evalDist] at he hf hs
  dsimp only [TargetCollisionResistance.advantage, TargetCollisionResistance.outputMeasure,
    SM_DT_TCR_Advantage, SM_DT_PRE_Advantage]
  nlinarith

private theorem selectedSourceMass_le_terminal_add_ud
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} ≤
      𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) := by
  have hdist := MeasureTheory.Measure.apply_true_le_add_boolDist
    𝒟[SM_DT_UD_Experiment .real (chainUndetectabilityReduction P enc K I hv hw A)]
    𝒟[SM_DT_UD_Experiment .ideal (chainUndetectabilityReduction P enc K I hv hw A)]
  exact finite_hybrid_boolDist_bound _ _ _ _ _ _
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (nativeBoolMass_ne_top _))
    (selectedSource_native_telescope P enc K I hv hw A) hdist

/-- The native active matching mass is bounded by the three actual original collision
advantages and the original-domain chain UD/PRE advantages, with exact active selector coefficients.
The absolute Boolean distance is taken after the signed native telescope. -/
theorem activeMatchingMass_le_advantages
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    let c : ℝ≥0∞ := (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ)
    𝒟[activeMatchingExperiment P enc K I A] {true} ≤
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction P enc K
            I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A) +
      c * SM_DT_PRE_Advantage (selectedChainPreimageReduction P enc K I hv hw A) +
      c * ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) := by
  have hrem := activeRemainderMass_eq_selectorCount_mul_selectedSourceMass P enc K I hv hw htwo A
  have hterminal := selectedSourceMass_le_terminal_add_ud P enc K I hv hw A
  have hpre := selectedPreimageMass_le_advantage P enc K I hv hw A
  have hchain : 𝒟[activeRemainderExperiment P enc K I A] {true} ≤
      ((((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        (SM_DT_PRE_Advantage (selectedChainPreimageReduction P enc K I hv hw A) +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A)) := by
    rw [hrem]
    gcongr
    exact hterminal.trans (add_le_add hpre le_rfl)
  calc
    _ ≤ 𝒟[encodingCollisionExperiment P enc K I A] {true} +
        𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] {true} +
        𝒟[chainCutCollisionExperiment P enc K I A] {true} +
        𝒟[activeRemainderExperiment P enc K I A] {true} :=
      activeMatchingMass_le_collision_masses_add_remainder P enc K I hv hw A
    _ ≤ _ := by
      have htotal := add_le_add (add_le_add (add_le_add
        (encodingCollisionMass_le_advantage P enc qs K I A hqueries)
        (sameMessageRandomizerChainCollisionMass_le_advantage P enc K I hv hw A))
        (chainCutCollisionMass_le_advantage P enc K I hv hw A)) hchain
      simpa only [ProbCompRuntime.probComp_evalDist, mul_add, mul_assoc, add_assoc] using htotal

/-- The actual selected terminal mass is bounded by fixed-fallback chain PRE, independently of
accidental fallback wins outside the selected event. No equality with the selected-coordinate
fallback PRE advantage is assumed. -/
theorem selectedPreimageMass_le_fixedFallbackAdvantage
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} ≤
      SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  change 𝒟[chainPRESelectedProgram P enc K I A] {true} ≤ _
  unfold SM_DT_PRE_Advantage
  rw [fixedFallbackPREExperiment_eq_explicit P enc K I hv hw A]
  unfold chainPRESelectedProgram fixedFallbackPREExplicitProgram
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro hidden _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out hout
  let guess := activeGuess I selector
  by_cases hselected : intervalSelectedChainObservation P enc K I fillers guess out = true
  · have heval := extractChainPreimageWithFallback_sound P enc K I A pp fillers guess
      (TweakableHash.eval P.thf pp
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (P.digestInput hidden))
      starts (starts 0 0) out hout hselected
    have hwin := heval
    simp only [show activeGuess I selector = guess from rfl, hselected, hwin,
      decide_true, evalDist_pure,
      MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton true)]
    simp
  · have hfalse := Bool.eq_false_iff.mpr hselected
    simp [show activeGuess I selector = guess from rfl, hfalse]

/-- The active matching branch is bounded by its three actual original collision reductions,
the actual fixed-fallback chain PRE advantage and the signed real-minus-ideal chain UD contribution.
The query bound counts every signing request, including failures, inactive requests and repeats. -/
theorem activeMatchingMass_le_signed_fixedFallback_advantages
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    let c : ℝ := (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ)
    (𝒟[activeMatchingExperiment P enc K I A] {true}).toReal ≤
      (TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A)).toReal +
      (SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction
          P enc K I A)).toReal +
      (SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A)).toReal +
      c * (SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A)).toReal +
      c * (2 ^ w - 1 : ℕ) *
        ((𝒟[SM_DT_UD_Experiment .real
          (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal -
        (𝒟[SM_DT_UD_Experiment .ideal
          (chainUndetectabilityReduction P enc K I hv hw A)] {true}).toReal) := by
  have hp := activeMatchingMass_le_collision_masses_add_remainder P enc K I hv hw A
  change 𝒟[activeMatchingExperiment P enc K I A] {true} ≤
    𝒟[encodingCollisionExperiment P enc K I A] {true} +
    𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] {true} +
    𝒟[chainCutCollisionExperiment P enc K I A] {true} +
    𝒟[activeRemainderExperiment P enc K I A] {true} at hp
  have hpReal := ENNReal.toReal_mono
    (add_ne_top.mpr ⟨add_ne_top.mpr ⟨add_ne_top.mpr
      ⟨nativeBoolMass_ne_top _, nativeBoolMass_ne_top _⟩, nativeBoolMass_ne_top _⟩,
      nativeBoolMass_ne_top _⟩) hp
  rw [ENNReal.toReal_add (by finiteness) (nativeBoolMass_ne_top _),
    ENNReal.toReal_add (by finiteness) (nativeBoolMass_ne_top _),
    ENNReal.toReal_add (nativeBoolMass_ne_top _) (nativeBoolMass_ne_top _),
    activeRemainderMass_eq_signed_terminal P enc K I hv hw htwo A] at hpReal
  have he := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (encodingCollisionMass_le_advantage P enc qs K I A hqueries)
  have hf := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (sameMessageRandomizerChainCollisionMass_le_advantage P enc K I hv hw A)
  have hs := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (chainCutCollisionMass_le_advantage P enc K I hv hw A)
  have hpre := ENNReal.toReal_mono (nativeBoolMass_ne_top _)
    (selectedPreimageMass_le_fixedFallbackAdvantage P enc K I hv hw A)
  have hc : (0 : ℝ) ≤ (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) := by positivity
  simp only [ProbCompRuntime.probComp_evalDist] at he hf hs
  dsimp only [TargetCollisionResistance.advantage, TargetCollisionResistance.outputMeasure,
    SM_DT_TCR_Advantage, SM_DT_PRE_Advantage]
  nlinarith

/-- The native active matching mass is bounded by the three actual original collision
advantages and the original-domain chain UD/PRE advantages, with exact active selector coefficients.
The absolute Boolean distance is taken after the signed native telescope. -/
theorem activeMatchingMass_le_fixedFallback_advantages
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    let c : ℝ≥0∞ := (((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ)
    𝒟[activeMatchingExperiment P enc K I A] {true} ≤
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction P enc K
            I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A) +
      c * SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) +
      c * ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) := by
  have hrem := activeRemainderMass_eq_selectorCount_mul_selectedSourceMass P enc K I hv hw htwo A
  have hterminal := selectedSourceMass_le_terminal_add_ud P enc K I hv hw A
  have hpre := selectedPreimageMass_le_fixedFallbackAdvantage P enc K I hv hw A
  have hchain : 𝒟[activeRemainderExperiment P enc K I A] {true} ≤
      ((((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        (SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A)) := by
    rw [hrem]
    gcongr
    exact hterminal.trans (add_le_add hpre le_rfl)
  calc
    _ ≤ 𝒟[encodingCollisionExperiment P enc K I A] {true} +
        𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] {true} +
        𝒟[chainCutCollisionExperiment P enc K I A] {true} +
        𝒟[activeRemainderExperiment P enc K I A] {true} :=
      activeMatchingMass_le_collision_masses_add_remainder P enc K I hv hw A
    _ ≤ _ := by
      have htotal := add_le_add (add_le_add (add_le_add
        (encodingCollisionMass_le_advantage P enc qs K I A hqueries)
        (sameMessageRandomizerChainCollisionMass_le_advantage P enc K I hv hw A))
        (chainCutCollisionMass_le_advantage P enc K I hv hw A)) hchain
      simpa only [ProbCompRuntime.probComp_evalDist, mul_add, mul_assoc, add_assoc] using htotal

end GXMSS.Interval.Unforgeability

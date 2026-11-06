/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening
import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening
public import HashSig.GXMSS.Security.Auxiliary.Interval.Interaction
import all HashSig.GXMSS.Security.Auxiliary.Interval.Interaction
public import HashSig.GXMSS.Security.Reductions.Interval.FillerGames
import all HashSig.GXMSS.Security.Reductions.Interval.FillerGames

/-!
# Measured partition of interval strong forgeries

Strong-valid source outputs split into four disjoint observations: active matching openings,
Merkle obstructions, inactive endpoint-vector openings and inactive child-pair openings. Their
native success masses sum to the strong-forgery mass without conditioning on execution success.
-/

public section

namespace GXMSS.Interval.Unforgeability

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval GXMSS.Interval.Filler
open SyncSignatureUnforgeability OracleSpec OracleComp TweakableHash Encoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- A fresh accepted active forgery recovers exactly the stored endpoint vector and mixed path. -/
@[expose] noncomputable def activeMatchingEvent
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : Bool :=
  let complete := sk.complete
  let (_, forgery, _) := out
  let (e, msg, sig) := forgery
  strongValid (GXMSS.Interval.scheme P enc K I) out &&
    match enc.value complete.seed msg sig.randomizer e with
    | none => false
    | some word =>
      let ys := fun i => P.chain complete.seed e i (word i)
        (2 ^ w - 1 - (word i).val) (sig.ots i)
      decide (Epoch.IsActive I e ∧
        (complete.endpoints e, GXMSS.IntervalMerkle.authPath P I complete.seed
          complete.endpoints sk.fillers e) = (ys, sig.path))

/-- A fresh accepted forgery differs from the honest active raw opening, or its inactive
computed-frontier digest differs from the actual committed filler. -/
@[expose] noncomputable def merkleObstructionEvent
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : Bool :=
  let complete := sk.complete
  let (_, forgery, _) := out
  let (e, msg, sig) := forgery
  strongValid (GXMSS.Interval.scheme P enc K I) out &&
    match enc.value complete.seed msg sig.randomizer e with
    | none => false
    | some word =>
      let ys := fun i => P.chain complete.seed e i (word i)
        (2 ^ w - 1 - (word i).val) (sig.ots i)
      if he : Epoch.IsActive I e then
        decide ((complete.endpoints e, GXMSS.IntervalMerkle.authPath P I complete.seed
          complete.endpoints sk.fillers e) ≠ (ys, sig.path))
      else decide (openingFrontierDigest P I complete.seed e ys sig.path ≠
        sk.fillers (frontierOf I e he))

/-- The pointwise strong-validity partition, with all six pairwise disjointness equations.
Consistency relates the observed public seed to the retained secret seed. In the inactive
matching branch the two family observations use the actual extractor and its returned payload. -/
theorem sourceStrongObservation_partition
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (hc : GXMSS.Interval.Consistent P I out.1 sk) :
    let complete := sk.complete
    let a := activeMatchingEvent P enc K I sk out
    let m := merkleObstructionEvent P enc K I sk out
    let fv := openingEvent P enc K I .endpointVector complete.seed sk.fillers out
    let fp := openingEvent P enc K I .childPair complete.seed sk.fillers out
    strongValid (GXMSS.Interval.scheme P enc K I) out = (a || m || fv || fp) ∧
      (a && m) = false ∧ (a && fv) = false ∧ (a && fp) = false ∧
      (m && fv) = false ∧ (m && fp) = false ∧ (fv && fp) = false := by
  obtain ⟨pk, ⟨e, msg, sig⟩, history⟩ := out
  let complete := sk.complete
  have hseed : pk.seed = complete.seed := hc.1
  dsimp only
  by_cases hv : strongValid (GXMSS.Interval.scheme P enc K I)
      (pk, (e, msg, sig), history) = true
  · cases hw : enc.value complete.seed msg sig.randomizer e with
    | none =>
      have hn : strongValid (GXMSS.Interval.scheme P enc K I)
          (pk, (e, msg, sig), history) = false := by
        simp [strongValid, GXMSS.Interval.scheme, GXMSS.Interval.verify, GXMSS.verify,
          hseed, hw]
      simp_all
    | some word =>
      dsimp only [complete] at hw
      by_cases he : Epoch.IsActive I e
      · simp [activeMatchingEvent, merkleObstructionEvent, openingEvent,
          extractFillerOpening, hv, hw, he]
        grind
      · by_cases hd : openingFrontierDigest P I complete.seed e
            (fun i => P.chain complete.seed e i (word i)
              (2 ^ w - 1 - (word i).val) (sig.ots i)) sig.path =
            sk.fillers (frontierOf I e he)
        · dsimp only [complete] at hd
          by_cases hz : frontierLevel I e = 0
          · simp [activeMatchingEvent, merkleObstructionEvent, openingEvent,
              extractFillerOpening, openingFrontierPreimage, familyOpening, HasFamily,
              frontierOf, hv, hw, he, hd, hz]
          · have hp : 0 < frontierLevel I e := Nat.pos_of_ne_zero hz
            simp [activeMatchingEvent, merkleObstructionEvent, openingEvent,
              extractFillerOpening, openingFrontierPreimage, familyOpening, HasFamily,
              frontierOf, hv, hw, he, hd, hz, hp]
        · dsimp only [complete] at hd
          simp [activeMatchingEvent, merkleObstructionEvent, openingEvent,
            extractFillerOpening, openingFrontierPreimage, hv, hw, he, hd]
  · have hf : strongValid (GXMSS.Interval.scheme P enc K I)
        (pk, (e, msg, sig), history) = false := Bool.eq_false_iff.mpr hv
    simp [activeMatchingEvent, merkleObstructionEvent, openingEvent,
      extractFillerOpening, hf]

/-- The actual keygen and synchronized adaptive view, with its secret retained only internally. -/
private noncomputable def retainedSource
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    ProbComp (GXMSS.Interval.SecretKey PP H h v I ×
      ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
        (GXMSS.Signature R H h v)) := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let out ← viewWithKeys P enc K I A pk sk
  pure (sk, out)

/-- Native Boolean experiment for the active matching branch of the source signing interaction. -/
@[expose] noncomputable def activeMatchingExperiment
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : ProbComp Bool := do
    let (pk, sk) ← GXMSS.Interval.keygen P I
    let out ← viewWithKeys P enc K I A pk sk
    pure (activeMatchingEvent P enc K I sk out)

/-- Native Boolean experiment for the Merkle obstruction branch of the source signing
interaction. -/
@[expose] noncomputable def merkleObstructionExperiment
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : ProbComp Bool := do
    let (pk, sk) ← GXMSS.Interval.keygen P I
    let out ← viewWithKeys P enc K I A pk sk
    pure (merkleObstructionEvent P enc K I sk out)

private theorem retainedSource_consistent
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (hr : (sk, out) ∈ support (retainedSource P enc K I A)) :
    GXMSS.Interval.Consistent P I out.1 sk := by
  simp only [retainedSource, GXMSS.Interval.keygen, bind_assoc, pure_bind] at hr
  obtain ⟨pp, _, hr⟩ := mem_support_bind_peel _ _ hr
  obtain ⟨starts, _, hr⟩ := mem_support_bind_peel _ _ hr
  obtain ⟨fillers, _, hr⟩ := mem_support_bind_peel _ _ hr
  obtain ⟨observed, hobs, hr⟩ := mem_support_bind_peel _ _ hr
  have heq := eq_of_mem_support_pure _ hr
  cases heq
  simp only [viewWithKeys] at hobs
  obtain ⟨result, _, hobs⟩ := mem_support_bind_peel _ _ hobs
  have heq := eq_of_mem_support_pure _ hobs
  cases heq
  exact GXMSS.Interval.consistent_keys P I pp starts fillers

/-- Integrating an exact continuation-mass identity preserves the complete returned mass.
The intermediate space is internal and deliberately given its discrete sigma algebra. -/
private theorem bind_true_mass_partition {α : Type} (draw : ProbComp α)
    (s a m fv fp : α → ProbComp Bool)
    (heq : ∀ x ∈ support draw, 𝒟[s x] {true} =
      𝒟[a x] {true} + 𝒟[m x] {true} + 𝒟[fv x] {true} + 𝒟[fp x] {true}) :
    𝒟[draw >>= s] {true} = 𝒟[draw >>= a] {true} + 𝒟[draw >>= m] {true} +
      𝒟[draw >>= fv] {true} + 𝒟[draw >>= fp] {true} := by
  let : MeasurableSpace α := ⊤
  simp only [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  simp only [← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
    Measurable fun x : α => 𝒟[a x] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun x : α => 𝒟[a x] {true} + 𝒟[m x] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun x : α => 𝒟[a x] {true} + 𝒟[m x] {true} + 𝒟[fv x] {true})]
  exact MeasureTheory.lintegral_congr_ae
    (evalDist.ae_of_forall_mem_support draw _ MeasurableSet.of_discrete heq)

/-- Exact native strong success is the sum of the four disjoint source observations.
Key generation and the entire adaptive signing interaction are unchanged; no execution mass
is conditioned on success or redrawn. -/
theorem strongAdvantage_eq_source_partition
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A =
      ProbCompRuntime.probComp.evalDist (activeMatchingExperiment P enc K I A) {true} +
        ProbCompRuntime.probComp.evalDist (merkleObstructionExperiment P enc K I A) {true} +
        ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A .endpointVector) {true} +
        ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A .childPair) {true} := by
  have hm := bind_true_mass_partition (retainedSource P enc K I A)
    (fun z => pure (strongValid (GXMSS.Interval.scheme P enc K I) z.2))
    (fun z => pure (activeMatchingEvent P enc K I z.1 z.2))
    (fun z => pure (merkleObstructionEvent P enc K I z.1 z.2))
    (fun z => let (sk, out) := z; let complete := sk.complete
      pure (openingEvent P enc K I .endpointVector complete.seed sk.fillers out))
    (fun z => let (sk, out) := z; let complete := sk.complete
      pure (openingEvent P enc K I .childPair complete.seed sk.fillers out)) ?_
  · simpa [strongAdvantage, strongUnforgeableExp, outputMeasure, interaction,
      activeMatchingExperiment, merkleObstructionExperiment, retainedSource,
      GXMSS.Interval.scheme, sourceOpening, viewWithKeys, map_eq_bind_pure_comp,
      monad_norm] using hm
  · rintro ⟨sk, out⟩ hr
    have hp := sourceStrongObservation_partition P enc K I sk out
      (retainedSource_consistent P enc K I A sk out hr)
    dsimp only at hp ⊢
    let complete := sk.complete
    cases hs : strongValid (GXMSS.Interval.scheme P enc K I) out <;>
      cases ha : activeMatchingEvent P enc K I sk out <;>
      cases hm : merkleObstructionEvent P enc K I sk out <;>
      cases hv : openingEvent P enc K I .endpointVector complete.seed sk.fillers out <;>
      cases hf : openingEvent P enc K I .childPair complete.seed sk.fillers out <;>
      simp_all [complete]

/-- Bound both inactive family-opening masses by their `udAdversary` and `preAdversary`
advantages. Active matching and Merkle obstruction masses retain coefficient one. -/
theorem strongAdvantage_le_merkle_active_and_filler_advantages
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A ≤
      ProbCompRuntime.probComp.evalDist (activeMatchingExperiment P enc K I A) {true} +
        ProbCompRuntime.probComp.evalDist (merkleObstructionExperiment P enc K I A) {true} +
        SM_DT_UD_Advantage (udAdversary P enc K I A .endpointVector) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A .endpointVector) +
        SM_DT_UD_Advantage (udAdversary P enc K I A .childPair) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A .childPair) := by
  rw [strongAdvantage_eq_source_partition]
  have hv := sourceOpening_le_advantages P enc K I A .endpointVector
  have hp := sourceOpening_le_advantages P enc K I A .childPair
  calc
    _ ≤ (ProbCompRuntime.probComp.evalDist (activeMatchingExperiment P enc K I A) {true} +
        ProbCompRuntime.probComp.evalDist (merkleObstructionExperiment P enc K I A) {true}) +
        (SM_DT_UD_Advantage (udAdversary P enc K I A .endpointVector) +
          SM_DT_PRE_Advantage (preAdversary P enc K I A .endpointVector)) +
        (SM_DT_UD_Advantage (udAdversary P enc K I A .childPair) +
          SM_DT_PRE_Advantage (preAdversary P enc K I A .childPair)) :=
      add_le_add (add_le_add_right hv _) hp
    _ = _ := by simp only [add_assoc]

end GXMSS.Interval.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Filler
import all HashSig.GXMSS.Interval.Filler
public import HashSig.GXMSS.Security.Auxiliary.Interval.Interaction
import all HashSig.GXMSS.Security.Auxiliary.Interval.Interaction
public import HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.Interval.MerkleWitnesses

/-!
# Typed observations of actual inactive filler openings
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval SyncSignatureUnforgeability
open OracleSpec OracleComp TweakableHash Encoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Package only a family-appropriate raw payload at the computed frontier. -/
@[expose] def familyOpening (f : Family) (I : Interval h) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) (raw : Sum (Fin v → H) (H × H)) :
    Option (Target f I × Input f H v) :=
  let node := frontierOf I e he
  match f, raw with
  | .endpointVector, .inl vector =>
    if hf : HasFamily .endpointVector node then some (⟨node, hf⟩, vector) else none
  | .childPair, .inr pair =>
    if hf : HasFamily .childPair node then some (⟨node, hf⟩, pair) else none
  | _, _ => none

/-- A packaged family's actual raw value hashes to its retained frontier digest. -/
theorem familyOpening_sound (P : HashInstance PP T X H h w v)
    (I : Interval h) (pp : PP) (fillers : Fillers I H) (f : Family)
    (e : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I e)
    (raw : Sum (Fin v → H) (H × H)) (n : Target f I) (input : Input f H v)
    (hp : RawFrontierPreimage P I pp e he fillers raw)
    (hr : familyOpening f I e he raw = some (n, input)) :
    TweakableHash.eval P.thf pp (tweak P n) (embed P f input) = fillers n.val := by
  cases f with
  | endpointVector =>
    cases raw with
    | inl vector =>
      simp only [familyOpening] at hr
      split at hr
      · cases Option.some.inj hr
        obtain ⟨hz, hhash⟩ := hp
        convert hhash using 1 <;>
          simp [tweak, address, embed, frontierOf, HashInstance.leafHash,
            frontierValue, hz]; rfl
      · simp at hr
    | inr pair => simp [familyOpening] at hr
  | childPair =>
    cases raw with
    | inl vector => simp [familyOpening] at hr
    | inr pair =>
      simp only [familyOpening] at hr
      split at hr
      · cases Option.some.inj hr
        obtain ⟨hz, hhash⟩ := hp
        convert hhash using 1 <;>
          simp [tweak, address, embed, frontierOf, HashInstance.nodeHash,
            frontierValue]; rfl
      · simp at hr

/-- Accepted, fresh, inactive source opening, with its actual vector or pair payload. -/
@[expose] noncomputable def extractFillerOpening
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (f : Family) (pp : PP) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : Option (Target f I × Input f H v) :=
  let (_, forgery, _) := out
  let (e, msg, sig) := forgery
  if strongValid (GXMSS.Interval.scheme P enc K I) out then
    if he : ¬ Epoch.IsActive I e then
      match enc.value pp msg sig.randomizer e with
      | none => none
      | some word =>
        let ys := fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i)
        (openingFrontierPreimage P I pp fillers e he ys sig.path).bind
          (familyOpening f I e he)
    else none
  else none

/-- For every complete endpoint array, the observation is the raw-preimage projection of
`GXMSS.Interval.MerkleWitnesses.extractInactiveOpening`, with the same validity and freshness tests.
-/
theorem extractFillerOpening_eq_projected_extractor
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (f : Family) (pp : PP) (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    extractFillerOpening P enc K I f pp fillers out =
      (let (_, forgery, _) := out
       let (e, msg, sig) := forgery
       if strongValid (GXMSS.Interval.scheme P enc K I) out then
         if he : ¬ Epoch.IsActive I e then
           match enc.value pp msg sig.randomizer e with
           | none => none
           | some word =>
             let ys := fun i => P.chain pp e i (word i)
               (2 ^ w - 1 - (word i).val) (sig.ots i)
             (match extractInactiveOpening P I pp xs fillers e he ys sig.path with
              | .inl raw => some raw
              | .inr _ => none).bind
                 (familyOpening f I e he)
         else none
       else none) := by
  simp only [extractFillerOpening, openingFrontierPreimage_eq_projection P I pp xs]
  rfl

/-- Every returned source payload is a preimage under the original target tweak and embedding. -/
theorem extractFillerOpening_sound
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (f : Family) (pp : PP) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (n : Target f I) (input : Input f H v)
    (hr : extractFillerOpening P enc K I f pp fillers out = some (n, input)) :
    TweakableHash.eval P.thf pp (tweak P n) (embed P f input) = fillers n.val := by
  obtain ⟨pk, ⟨e, msg, sig⟩, history⟩ := out
  dsimp only [extractFillerOpening] at hr
  split at hr
  · split at hr
    · rename_i he
      split at hr
      · simp at hr
      · rename_i word hword
        simp only [Option.bind_eq_some_iff] at hr
        obtain ⟨raw, hraw, hfamily⟩ := hr
        exact familyOpening_sound P I pp fillers f e he raw n input
          (openingFrontierPreimage_sound P I pp fillers e he _ sig.path raw hraw) hfamily
    · simp at hr
  · simp at hr

/-- Boolean observation of the actual extracted family payload. -/
@[expose] noncomputable def openingEvent
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (f : Family) (pp : PP) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) : Bool :=
  (extractFillerOpening P enc K I f pp fillers out).isSome

/-- The original ideal source key generation and adaptive interaction, retaining its filler table
only for the final family-opening observation. -/
@[expose] noncomputable def sourceOpening
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : ProbComp Bool := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let out ← viewWithKeys P enc K I A pk sk
  let complete := sk.complete
  pure (openingEvent P enc K I f complete.seed sk.fillers out)

/-- Expanding actual key generation retains the same sampled starts and complete filler table. -/
theorem sourceOpening_eq_keys_view
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    sourceOpening P enc K I A f = (do
      let pp ← TweakableHash.seedGen P.thf
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      let out ← viewFromKeys P enc K I A pp starts fillers
      pure (openingEvent P enc K I f pp fillers out)) := by
  simp [sourceOpening, GXMSS.Interval.keygen, viewFromKeys,
    GXMSS.Interval.keys, GXMSS.keys, monad_norm]

/-- The whole native source-opening measure after commuting independent fillers and starts. -/
theorem sourceOpening_measure_eq_fillers_view
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A f) =
      ProbCompRuntime.probComp.evalDist (do
        let pp ← TweakableHash.seedGen P.thf
        let fillers ← sampleFillers I H
        let out ← view P enc K I A pp fillers
        pure (openingEvent P enc K I f pp fillers out)) := by
  simp only [ProbCompRuntime.probComp_evalDist, sourceOpening_eq_keys_view, view, bind_assoc]
  apply evalDist_bind_congr_of_support
  intro pp _
  exact OracleComp.evalDist_bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H)
    (fun starts fillers => do
      let out ← viewFromKeys P enc K I A pp starts fillers
      pure (openingEvent P enc K I f pp fillers out))

/-- The empty target type forces every full-range extracted opening to be none. -/
@[simp] theorem extractFillerOpening_full
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (f : Family)
    (pp : PP) (fillers : Fillers (Interval.full h) H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    extractFillerOpening P enc K (Interval.full h) f pp fillers out = none := by
  cases hx : extractFillerOpening P enc K (Interval.full h) f pp fillers out with
  | none => rfl
  | some result => exact isEmptyElim result.1

/-- Every returned full-range view has a false filler-opening observation. -/
@[simp] theorem openingEvent_full
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (f : Family)
    (pp : PP) (fillers : Fillers (Interval.full h) H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    openingEvent P enc K (Interval.full h) f pp fillers out = false := by
  simp [openingEvent]

end GXMSS.Interval.Filler

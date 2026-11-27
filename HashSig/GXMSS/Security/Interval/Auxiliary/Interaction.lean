/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Whole adaptive interval signing interaction
-/

public section

namespace GXMSS.Interval

open GXMSS.IntervalMerkle SyncSignatureUnforgeability OracleSpec OracleComp
open TweakableHash IncomparableEncoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The adaptive suffix runs `signingOracle` with the interval scheme and supplied secret key. -/
@[expose] noncomputable def viewWithKeys [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.Interval.SecretKey PP H h v I) :
    ProbComp (ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) := do
  let (forgery, history) ← runWithSigningOracle (GXMSS.Interval.scheme P enc K I) sk
    (A.forge pk) emptyHistory
  pure (pk, forgery, history)

/-- Fixed-key adaptive view using `signingOracle` and an empty signing history. -/
@[expose] noncomputable def viewFromKeys [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) :
    ProbComp (ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) := do
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  viewWithKeys P enc K I A pk sk

/-- Sample starts once and retain the same complete filler table throughout the view. -/
@[expose] noncomputable def view [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (pp : PP) (fillers : Fillers I H) :
    ProbComp (ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) := do
  let starts ← GXMSS.sampleStarts H h v
  viewFromKeys P enc K I A pp starts fillers

/-- Expand the actual source interaction without changing its random draws or handler. -/
theorem interaction_eq_keys_view [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    interaction (GXMSS.Interval.scheme P enc K I) A = (do
      let pp ← TweakableHash.seedGen P.thf
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      viewFromKeys P enc K I A pp starts fillers) := by
  simp [interaction, GXMSS.Interval.scheme, GXMSS.Interval.keygen, viewFromKeys,
    viewWithKeys, monad_norm]

/-- Whole source-view measure after commuting the independent filler and start samplers.
The native endpoint preserves every returned view, including failed and repeated requests. -/
theorem interaction_measure_eq_fillers_view
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    let : MeasurableSpace (ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) := ⊤
    ProbCompRuntime.probComp.evalDist (interaction (GXMSS.Interval.scheme P enc K I) A) =
      ProbCompRuntime.probComp.evalDist (do
        let pp ← TweakableHash.seedGen P.thf
        let fillers ← sampleFillers I H
        view P enc K I A pp fillers) := by
  let : MeasurableSpace (ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
    (GXMSS.Signature R H h v)) := ⊤
  simp only [ProbCompRuntime.probComp_evalDist, interaction_eq_keys_view, view]
  apply evalDist_bind_congr_of_support
  intro pp _
  exact OracleComp.evalDist_bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H)
    (fun starts fillers => viewFromKeys P enc K I A pp starts fillers)

end GXMSS.Interval

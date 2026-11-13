/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.FillerGames.Reductions
import HashSig.GXMSS.Security.Interval.Reductions.FillerGames.Setup
import all HashSig.GXMSS.Security.Interval.Reductions.FillerGames.Reductions
import HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets

/-!
# Filler-opening advantage bounds

Each family opening is bounded by its actual UD/PRE terms without conditioning on termination.
Full-range experiments retain their seed draw while their returned true mass is zero.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval
open SyncSignatureUnforgeability OracleSpec OracleComp TweakableHash IncomparableEncoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Each family's ideal product-response opening event has one actual UD and one actual PRE term.
This inequality concerns only the extracted filler-opening event. -/
private theorem hybrid_ideal_le_advantages
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .ideal) {true} ≤
      SM_DT_UD_Advantage (udAdversary P enc K I A f) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
  simp only [ProbCompRuntime.probComp_evalDist]
  have hreal : 𝒟[hybrid P enc K I A f .real] =
      𝒟[SM_DT_PRE_Experiment (preAdversary P enc K I A f)] := by
    simpa only [ProbCompRuntime.probComp_evalDist] using
      hybrid_real_measure_eq_preExperiment P enc K I A f
  have hmass : 𝒟[hybrid P enc K I A f .real] {true} =
      SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
    rw [hreal]
    rfl
  have hdist : (𝒟[hybrid P enc K I A f .ideal]).boolDist
      𝒟[hybrid P enc K I A f .real] =
      SM_DT_UD_Advantage (udAdversary P enc K I A f) := by
    rw [MeasureTheory.Measure.boolDist_comm,
      ← udExperiment_eq_hybrid P enc K I A f .real,
      ← udExperiment_eq_hybrid P enc K I A f .ideal]
    rfl
  simpa only [hmass, hdist, add_comm] using
    MeasureTheory.Measure.apply_true_le_add_boolDist
      𝒟[hybrid P enc K I A f .ideal] 𝒟[hybrid P enc K I A f .real]


/-- The ideal hybrid and actual ideal source have the same entire Boolean opening measure. -/
private theorem hybrid_ideal_measure_eq_sourceOpening
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .ideal) =
      ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A f) := by
  rw [sourceOpening_measure_eq_fillers_view]
  simp only [ProbCompRuntime.probComp_evalDist, hybrid_ideal_measure_eq_tables]
  apply evalDist_bind_congr_of_support
  intro pp _
  let : MeasurableSpace H := ⊤
  let next (fillers : Fillers I H) : ProbComp Bool := do
    let out ← view P enc K I A pp fillers
    pure (openingEvent P enc K I f pp fillers out)
  have htables : 𝒟[(do
      let selected ← (sampleTable f I : ProbComp (Target f I → H))
      let other ← sampleTable f.other I
      pure (assemble f I selected other)) >>= next] = 𝒟[sampleFillers I H >>= next] := by
    rw [evalDist_bind_of_discrete, assemble_tables_measure, ← evalDist_bind_of_discrete]
  simpa only [bind_assoc, pure_bind] using htables

/-- An ideal source filler opening is bounded by the actual original-hash UD and PRE adversaries,
with coefficient one and the exact selected-family multi-target capacity. -/
theorem sourceOpening_le_advantages
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A f) {true} ≤
      SM_DT_UD_Advantage (udAdversary P enc K I A f) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
  rw [← hybrid_ideal_measure_eq_sourceOpening]
  exact hybrid_ideal_le_advantages P enc K I A f


/-- Full-range registration makes no challenge query, for either family. -/
private theorem collectTargets_full (P : HashInstance PP T X H h w v) (f : Family) :
    collectTargets P f (Interval.full h) (targetList f (Interval.full h)) = pure (some []) := by
  simp [collectTargets]

private theorem native_bind_false {S : Type} (draw : ProbComp S) (next : S → ProbComp Bool)
    (hn : ∀ x, 𝒟[next x] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[draw >>= next] = 𝒟[(pure false : ProbComp Bool)] :=
  (evalDist_bind_congr draw next (fun _ => pure false) hn).trans
    (OracleComp.evalDist_bind_const draw (pure false))

/-- Both full-range hybrid worlds have exactly the returned-false Boolean measure. -/
private theorem hybrid_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    𝒟[hybrid P enc K (Interval.full h) A f world] = 𝒟[(pure false : ProbComp Bool)] := by
  have hcont (pp : PP) (st : Option (Setup f (Interval.full h) H)) :
      𝒟[(udAdversary P enc K (Interval.full h) A f).distinguish st pp] =
        𝒟[(pure false : ProbComp Bool)] := by
    cases st with
    | none => rfl
    | some st => simp [udAdversary, openingEvent_full]
  calc
    _ = 𝒟[(do
      let pp ← TweakableHash.seedGen P.thf
      let answers ← sampleResponses P (Interval.full h) f world pp (targetList f (Interval.full h))
      let _ ← completeSetup f (Interval.full h) answers
      pure false : ProbComp Bool)] := by
        unfold hybrid
        apply evalDist_bind_congr_of_support
        intro pp _
        apply evalDist_bind_congr_of_support
        intro answers _
        apply evalDist_bind_congr_of_support
        intro st _
        exact hcont pp st
    _ = _ := by
      apply native_bind_false
      intro pp
      apply native_bind_false
      intro answers
      exact OracleComp.evalDist_bind_const _ _

/-- The actual full-range UD experiments both return false with total mass one. -/
theorem udExperiment_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world (udAdversary P enc K (Interval.full h) A f)] =
      𝒟[(pure false : ProbComp Bool)] := by
  rw [udExperiment_eq_hybrid, hybrid_full_measure]

/-- The actual full-range PRE experiment returns false with total mass one. -/
theorem preExperiment_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    𝒟[SM_DT_PRE_Experiment (preAdversary P enc K (Interval.full h) A f)] =
      𝒟[(pure false : ProbComp Bool)] := by
  have heq := hybrid_real_measure_eq_preExperiment P enc K (Interval.full h) A f
  simp only [ProbCompRuntime.probComp_evalDist] at heq
  rw [← heq, hybrid_full_measure]

/-- Full-range actual UD advantage is zero for each empty target family. -/
@[simp] theorem udAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_UD_Advantage (udAdversary P enc K (Interval.full h) A f) = 0 := by
  simp [SM_DT_UD_Advantage, udExperiment_full_measure]

/-- Full-range actual PRE advantage is zero for each empty target family. -/
@[simp] theorem preAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_PRE_Advantage (preAdversary P enc K (Interval.full h) A f) = 0 := by
  simp [SM_DT_PRE_Advantage, preExperiment_full_measure]

end GXMSS.Interval.Filler

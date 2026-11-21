/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.FillerGames.Setup
import all HashSig.GXMSS.Security.Interval.Reductions.FillerGames.Setup
import HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets

/-!
# Adaptive filler reduction programs

Named UD/PRE adversaries run the actual signing view with one persistent frontier table.
Whole output laws compare their original hash responses with explicit retained-table hybrids.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval
open SyncSignatureUnforgeability OracleSpec OracleComp TweakableHash IncomparableEncoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The actual UD adversary: pre-seed registration, retained-table view, then the opening event. -/
noncomputable def udAdversary
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : SM_DT_UD_Adversary (udProblem P I f) where
  State := Option (Setup f I H)
  pick := setup P f I
  distinguish state pp := match state with
    | none => pure false
    | some st => do
      let out ← view P enc K I A pp st.fillers
      pure (openingEvent P enc K I f pp st.fillers out)

/-- The actual PRE adversary returns the accepted target and the extracted original input.
Failure emits the out-of-range capacity sentinel and a properly sampled family input. -/
noncomputable def preAdversary
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : SM_DT_PRE_Adversary (preProblem P I f) where
  State := Option (Setup f I H)
  choose := setup P f I
  invert state pp := do
    let result ← match state with
      | none => pure none
      | some st => do
        let out ← view P enc K I A pp st.fillers
        pure (extractFillerOpening P enc K I f pp st.fillers out)
    match result with
    | some (n, input) => pure (targetIndex n, input)
    | none => do
      let input ← $ᵗ Input f H v
      pure (targetCapacity f I, input)

/-- Every accepted target position names its original tweak in the hidden PRE transcript. -/
private theorem hidden_target_lookup [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I))) (n : Target f I) :
    ∃ sampled, hidden[targetIndex n]? = some (tweak P n, sampled) := by
  have ht := sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh
  have hi : targetIndex n < (targetList f I).length := by simpa using targetIndex_lt n
  have hl : (hidden[targetIndex n]?).map Prod.fst = some (tweak P n) := by
    rw [← List.getElem?_map, ht, List.getElem?_map, List.getElem?_eq_getElem hi,
      targetList_getElem_targetIndex]
    rfl
  cases hx : hidden[targetIndex n]? with
  | none => simp [hx] at hl
  | some entry =>
    obtain ⟨t, sampled⟩ := entry
    simp only [hx, Option.map_some, Option.some.injEq] at hl
    subst t
    exact ⟨sampled, rfl⟩

/-- The retained response at an accepted target is the image of that target's hidden PRE input. -/
private theorem completeSetup_target_image [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) (pp : PP)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I)))
    (st : Setup f I H)
    (hs : some st ∈ support (completeSetup f I (hiddenImages P f pp hidden)))
    (n : Target f I) :
    ∃ sampled, hidden[targetIndex n]? = some (tweak P n, sampled) ∧
      TweakableHash.eval P.thf pp (tweak P n) (embed P f sampled) = st.fillers n.val := by
  obtain ⟨sampled, hx⟩ := hidden_target_lookup P I f hidden hh n
  refine ⟨sampled, hx, ?_⟩
  have hi := completeSetup_lookup f I (hiddenImages P f pp hidden) st hs n
  simpa only [hiddenImages, List.getElem?_map, hx, Option.map_some, Option.some.injEq] using hi

/-- The fallback index is outside the full accepted PRE transcript. -/
private theorem hidden_sentinel_lookup [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I))) :
    hidden[targetCapacity f I]? = none := by
  have ht := congrArg List.length (sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh)
  have hl : hidden.length = targetCapacity f I := by simpa using ht
  simp [← hl]

/-- Explicit product-response hybrid followed by the actual retained-table UD continuation. -/
private noncomputable def hybrid
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← TweakableHash.seedGen P.thf
  let answers ← sampleResponses P I f world pp (targetList f I)
  let st ← completeSetup f I answers
  (udAdversary P enc K I A f).distinguish st pp

/-- Both entire Boolean UD output laws agree with the explicit product-response hybrids. -/
private theorem udExperiment_eq_hybrid
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (udAdversary P enc K I A f) = hybrid P enc K I A f world := by
  change (do
    let pp ← TweakableHash.seedGen P.thf
    let (st, _, _) ← (simulateQ (udOracle P I f world pp) (setup P f I)).run ([], [])
    (udAdversary P enc K I A f).distinguish st pp) = _
  simp only [setup_run_ud, bind_assoc, pure_bind, hybrid]

/-- The authoritative PRE winning check on a retained hidden transcript. -/
private def preCheck [DecidableEq H] (P : HashInstance PP T X H h w v)
    (f : Family) (pp : PP) (hidden : List (T × Input f H v)) (guess : ℕ × Input f H v) : Bool :=
  let (j, input) := guess
  match hidden[j]? with
  | none => false
  | some (t, sampled) => decide (TweakableHash.eval P.thf pp t (embed P f input) =
      TweakableHash.eval P.thf pp t (embed P f sampled))

/-- The ideal hybrid has the joint law of both independently sampled complete family tables. -/
private theorem hybrid_ideal_measure_eq_tables
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    𝒟[hybrid P enc K I A f .ideal] = 𝒟[(do
      let pp ← TweakableHash.seedGen P.thf
      let selected ← sampleTable f I
      let other ← sampleTable f.other I
      let fillers := assemble f I selected other
      let out ← view P enc K I A pp fillers
      pure (openingEvent P enc K I f pp fillers out))] := by
  unfold hybrid
  simp only [sampleResponses_ideal_eq_replicate, length_targetList, replicate_eq_ofFn_mOfFn,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, completeSetup_ofFn,
    udAdversary, Setup.fillers]
  apply evalDist_bind_congr_of_support
  intro pp _
  exact orderedTable_bind_eq_table f I (fun selected => do
    let other ← sampleTable f.other I
    let fillers := assemble f I selected other
    let out ← view P enc K I A pp fillers
    pure (openingEvent P enc K I f pp fillers out))

/-- Explicit PRE experiment retaining the full hidden-input transcript until its winning check. -/
private noncomputable def preExplicit
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : ProbComp Bool := do
  let pp ← TweakableHash.seedGen P.thf
  let hidden ← sampleHiddenInputs P I f (targetList f I)
  let st ← completeSetup f I (hiddenImages P f pp hidden)
  let guess ← (preAdversary P enc K I A f).invert st pp
  pure (preCheck P f pp hidden guess)

/-- The authoritative PRE experiment has exactly the explicit joint hidden-transcript law. -/
private theorem preExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_PRE_Experiment (preAdversary P enc K I A f) = preExplicit P enc K I A f := by
  have hrun (pp : PP) :
      (simulateQ (SM_DT_PRE_oracles (preProblem P I f) pp)
        (preAdversary P enc K I A f).choose).run ([], []) =
        (do
          let hidden ← sampleHiddenInputs P I f (targetList f I)
          let st ← completeSetup f I (hiddenImages P f pp hidden)
          pure (st, (hidden, []))) := setup_run_pre P I f pp
  unfold SM_DT_PRE_Experiment preExplicit
  simp only [hrun, bind_assoc, pure_bind]
  simp only [preProblem, SM_DT_PRE_Problem.standalone]
  apply bind_congr
  intro pp
  apply bind_congr
  intro hidden
  apply bind_congr
  intro st
  apply bind_congr
  intro guess
  obtain ⟨j, input⟩ := guess
  cases hx : hidden[j]? with
  | none => simp [preCheck, hx]
  | some entry => cases entry; simp [preCheck, hx]; rfl


/-- On a valid retained PRE setup, actual inversion has the entire opening-observation law.
The none branch loses via the sentinel; its proper input sample is lossless in native ProbComp. -/
private theorem preContinuation_measure_eq_observation
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (pp : PP)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I)))
    (st : Setup f I H)
    (hs : some st ∈ support (completeSetup f I (hiddenImages P f pp hidden))) :
    𝒟[(preAdversary P enc K I A f).invert (some st) pp >>=
      fun guess => pure (preCheck P f pp hidden guess)] =
      𝒟[(udAdversary P enc K I A f).distinguish (some st) pp] := by
  simp only [preAdversary, udAdversary, pure_bind, bind_assoc]
  apply evalDist_bind_congr_of_support
  intro out _
  cases hx : extractFillerOpening P enc K I f pp st.fillers out with
  | none =>
    simp only [preCheck, openingEvent, hx, Option.isSome_none]
    simp only [bind_assoc, pure_bind, hidden_sentinel_lookup P I f hidden hh]
    exact OracleComp.evalDist_bind_const ($ᵗ Input f H v) (pure false)
  | some result =>
    obtain ⟨n, input⟩ := result
    obtain ⟨sampled, hi, himage⟩ := completeSetup_target_image P I f pp hidden hh st hs n
    have hpre := extractFillerOpening_sound P enc K I f pp st.fillers out n input hx
    have hhash : TweakableHash.eval P.thf pp (tweak P n) (embed P f input) =
        TweakableHash.eval P.thf pp (tweak P n) (embed P f sampled) := hpre.trans himage.symm
    simp [hx, preCheck, hi, hhash, openingEvent]


/-- The real product-response hybrid and the actual PRE adversary have identical Boolean laws. -/
private theorem hybrid_real_measure_eq_preExperiment
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .real) =
      ProbCompRuntime.probComp.evalDist (SM_DT_PRE_Experiment (preAdversary P enc K I A f)) := by
  simp only [ProbCompRuntime.probComp_evalDist, preExperiment_eq_explicit]
  unfold hybrid preExplicit
  simp only [sampleResponses_real_eq_hiddenImages, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro pp _
  apply evalDist_bind_congr_of_support
  intro hidden hh
  apply evalDist_bind_congr_of_support
  intro st hs
  cases st with
  | none =>
    have ht := congrArg List.length (sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh)
    have hl : (hiddenImages P f pp hidden).length = targetCapacity f I := by
      simpa [hiddenImages] using ht
    exact (completeSetup_ne_none f I _ hl none hs rfl).elim
  | some st =>
    exact (preContinuation_measure_eq_observation P enc K I A f pp hidden hh st hs).symm

end GXMSS.Interval.Filler

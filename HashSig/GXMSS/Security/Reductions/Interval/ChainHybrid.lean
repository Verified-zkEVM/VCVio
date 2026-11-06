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
public import HashSig.GXMSS.Security.Reductions.Experiments
import all HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
public import HashSig.GXMSS.Security.Reductions.Interval.FillerGames
import all HashSig.GXMSS.Security.Reductions.Interval.FillerGames
public import HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.Interval.SourcePartition
import all HashSig.GXMSS.Security.Reductions.Interval.SourcePartition
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation

/-!
# Selected interval chain hybrids

The original-domain chain UD/PRE strategies and native selected-source telescope share the actual
interval simulator and one sampled filler table. Their returned observations preserve failures
and missing mass. The declarations have the `VerifiedGXMSS.IntervalChainSecurity` namespace.
-/

public section

namespace GXMSS.Interval.Reductions.Chain
open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle Encoding
open ENNReal
open GXMSS.Reductions GXMSS.Unforgeability GXMSS.Interval.Reductions SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

private abbrev ActiveSelector (I : Interval h) (w v : ℕ) :=
  Fin (I.last.val - I.first.val + 1) × Fin v × Fin (2 ^ w - 1)

private def activeGuess (I : Interval h) (selector : ActiveSelector I w v) : Guess h w v :=
  let (offset, chain, position) := selector
  (⟨I.first.val + offset.val, by
    have ho := I.ordered
    have hl := I.last.isLt
    have hx := offset.isLt
    simp only [Fin.le_iff_val_le_val] at ho
    omega⟩, chain, position)

private theorem activeGuess_isActive (I : Interval h) (selector : ActiveSelector I w v) :
    Epoch.IsActive I (guessedEpoch (activeGuess I selector)) := by
  rcases selector with ⟨offset, chain, position⟩
  have ho := I.ordered
  have hx := offset.isLt
  simp only [Epoch.IsActive, activeGuess, guessedEpoch, Fin.le_iff_val_le_val] at *
  omega

private theorem activeSelector_card (I : Interval h) :
    Fintype.card (ActiveSelector I w v) =
      (I.last.val - I.first.val + 1) * v * (2 ^ w - 1) := by
  simp [ActiveSelector, Nat.mul_assoc]

private structure ChainUDState (H : Type) (h w v : ℕ) (I : Interval h) where
  selector : ActiveSelector I w v
  hybrid : Fin (2 ^ w - 1)
  answer : Option H
  starts : Epoch h → Fin v → H
  fillers : Fillers I H

private structure ChainPREState (H : Type) (h w v : ℕ) (I : Interval h) where
  selector : ActiveSelector I w v
  answer : Option H
  starts : Epoch h → Fin v → H
  fillers : Fillers I H

private noncomputable def chainUDPick
    [SampleableType H] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem P).thColl)) (ChainUDState H h w v I) := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let selector ← OracleComp.liftComp ($ᵗ (ActiveSelector I w v)) _
    let hybrid ← OracleComp.liftComp ($ᵗ (Fin (2 ^ w - 1))) _
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let fillers ← OracleComp.liftComp (sampleFillers I H) _
    let guess := activeGuess I selector
    let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem P).thColl)).query (.inr (.inl
        (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid)))))
    return ⟨selector, hybrid, answer, starts, fillers⟩

/-- Original-domain interval UD retains the active selector, hybrid cut, starts and the entire
filler table are retained before the sole challenge; the actual adaptive view uses that table. -/
noncomputable def chainUndetectabilityReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Adversary (chainUDProblem P) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact {
    State := ChainUDState H h w v I
    pick := chainUDPick P I
    distinguish state pp := do
      let guess := activeGuess I state.selector
      let hybrid := state.hybrid
      if hybrid.val < (guessedPosition guess).val then
        match state.answer with
        | none => return false
        | some response =>
          let splice : Guess h w v :=
            (guessedEpoch guess, guessedChain guess, state.hybrid)
          let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
            A pp splice response state.starts
          return intervalSelectedChainObservation P enc K I state.fillers guess out
      else return false }

private theorem chainUD_real_response_bind_chain
    [SampleableType H] {α : Type} [MeasurableSpace α]
    (P : HashInstance PP T X H h w v) (pp : PP)
    (epoch : Epoch h) (chain : Fin v) (position : Fin (2 ^ w - 1))
    (f : H → ProbComp α) :
    𝒟[SM_DT_UD_response .real (chainUDProblem P) pp
      (P.chainTweak (epoch, chain, position)) >>= f] =
    𝒟[do let x ← ($ᵗ H : ProbComp H); f (P.chain pp epoch chain position.val 1 x)] := by
  unfold SM_DT_UD_response chainUDProblem SM_DT_UD_Problem.standalone
  simp only [bind_assoc, pure_bind]
  have hstep (x : H) : TweakableHash.eval P.thf pp (P.chainTweak (epoch, chain, position))
      (P.digestInput x) = P.chain pp epoch chain position.val 1 x := by
    have hs := P.chain_succ pp epoch chain position.val 0 x (by omega)
    simpa only [Nat.add_zero, zero_add, P.chain_zero] using hs.symm
  simp_rw [hstep]

private theorem chainUD_ideal_response [SampleableType H]
    (P : HashInstance PP T X H h w v) (pp : PP) (tweak : T) :
    SM_DT_UD_response .ideal (chainUDProblem P) pp tweak =
      ($ᵗ H : ProbComp H) := rfl

private noncomputable def extractChainPreimageWithFallback
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (guess : Guess h w v) (fallback : H)
    (out : Result PP H M R h v) : H :=
  let pk := out.pk
  if intervalSelectedChainObservation P enc K I fillers guess out = false then fallback
  else
    let (epoch, message, signature) := out.forgery
    match out.history epoch with
    | some (first, some honest) =>
      match enc.value pk.seed first honest.randomizer epoch,
          enc.value pk.seed message signature.randomizer epoch with
      | some honestWord, some forgedWord =>
        match GXMSS.Security.findSmallerCoordinate honestWord forgedWord with
        | none => fallback
        | some i =>
          match P.findChainCut pk.seed epoch i (forgedWord i) (honestWord i)
              (2 ^ w - 1) (honest.ots i) (signature.ots i) with
          | some (.inl preimage) => preimage
          | _ => fallback
      | _, _ => fallback
    | _ =>
      match enc.value pk.seed message signature.randomizer epoch with
      | none => fallback
      | some word =>
        match findNonMaximumCoordinate word with
        | none => fallback
        | some i => P.chain pk.seed epoch i (word i)
            (2 ^ w - 2 - (word i).val) (signature.ots i)

private noncomputable def extractChainPreimage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (fillers : Fillers I H) (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v) : H :=
  extractChainPreimageWithFallback P enc K I fillers guess
    (starts (guessedEpoch guess) (guessedChain guess)) out

private noncomputable def chainPREPick
    [SampleableType H] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem P).thColl)) (ChainPREState H h w v I) := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let selector ← OracleComp.liftComp ($ᵗ (ActiveSelector I w v)) _
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let fillers ← OracleComp.liftComp (sampleFillers I H) _
    let guess := activeGuess I selector
    let answer ← liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem P).thColl)).query (.inr (.inl
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)))))
    return ⟨selector, answer, starts, fillers⟩

/-- Interval PRE on the original digest input domain with a selected-coordinate fallback.
Every simulated view and chain cut uses one retained filler table. -/
noncomputable def selectedChainPreimageReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Adversary (chainPREProblem P) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact {
    State := ChainPREState H h w v I
    choose := chainPREPick P I
    invert state pp := do
      let guess := activeGuess I state.selector
      let fallback := state.starts (guessedEpoch guess) (guessedChain guess)
      match state.answer with
      | none => return (0, fallback)
      | some response =>
        let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
          A pp guess response state.starts
        let preimage := extractChainPreimage P enc K I state.fillers guess state.starts out
        return (0, preimage) }

private noncomputable def chainUDExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let response ← SM_DT_UD_response world (chainUDProblem P) pp
      (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid))
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
        A pp splice response starts
      pure (intervalSelectedChainObservation P enc K I fillers guess out)
    else pure false

private noncomputable def chainUDFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let response ← SM_DT_UD_response world (chainUDProblem P) pp
      (P.chainTweak (guessedEpoch guess, guessedChain guess, hybrid))
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false

private noncomputable def chainUDChainCutProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let guess := activeGuess I selector
    let x ← ($ᵗ H : ProbComp H)
    let response := match world with
      | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
      | .ideal => x
    if hybrid.val < (guessedPosition guess).val then
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, hybrid)
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess splice response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false

private theorem chainUDOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) {S : Type} (oa : ProbComp S)
    (state : SM_DT_UD_State T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem P) pp)
      (OracleComp.liftComp oa _)).run state =
        (fun x => (x, state)) <$> oa := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem chainUDOracles_challenge
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v)
    (world : SM_DT_UD_World) (pp : PP) (t : T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem P) pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (chainUDProblem P).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_UD_State T) =
      (fun answer => (some answer, ([t], []))) <$>
        SM_DT_UD_response world (chainUDProblem P) pp t := by
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_query_right,
    QueryImpl.add_apply_inl]
  simp [SM_DT_UD_challengeOracle, TweakFresh, TweakReserved, chainUDProblem,
    SM_DT_UD_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem chainUDExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (chainUndetectabilityReduction P enc K I hv hw A) =
      (letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
       letI : NeZero (2 ^ w - 1) := ⟨by
         have := Nat.one_lt_two_pow (by omega : w ≠ 0)
         omega⟩
       chainUDExplicitProgram P enc K I A world) := by
  unfold SM_DT_UD_Experiment chainUndetectabilityReduction chainUDExplicitProgram chainUDPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainUDOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainUDOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

private theorem chainUDExplicit_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDExplicitProgram P enc K I A world] {true} =
      𝒟[chainUDFilteredProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDExplicitProgram chainUDFilteredProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro hybrid
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro fillers
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro response
  let guess := activeGuess I selector
  by_cases hj : hybrid.val < (guessedPosition guess).val
  · simp only [show activeGuess I selector = guess from rfl, hj, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess
        (guessedEpoch guess, guessedChain guess, hybrid) response starts
  · simp only [show activeGuess I selector = guess from rfl, hj, ↓reduceIte]

private theorem chainUDFiltered_mass_eq_chainCut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDFilteredProgram P enc K I A world] {true} =
      𝒟[chainUDChainCutProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDFilteredProgram chainUDChainCutProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro hybrid
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro fillers
  let guess := activeGuess I selector
  let continuation : H → ProbComp Bool := fun response =>
    if hybrid.val < (guessedPosition guess).val then do
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess (guessedEpoch guess, guessedChain guess, hybrid) response starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
    else pure false
  cases world with
  | real =>
    exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
      (chainUD_real_response_bind_chain P pp (guessedEpoch guess) (guessedChain guess)
        hybrid continuation)
  | ideal => rfl

private theorem chainUDExperiment_true_eq_chainCut
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[chainUDChainCutProgram P enc K I A world] {true} := by
  rw [chainUDExperiment_eq_explicit]
  exact (chainUDExplicit_mass_eq_filtered P enc K I A world).trans
    (chainUDFiltered_mass_eq_chainCut P enc K I A world)

private theorem intervalFinalPreimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true)
    (word : Codeword v (2 ^ w)) (i : Fin v)
    (hword : let pk := out.pk
      let (epoch, message, signature) := out.forgery
      enc.value pk.seed message signature.randomizer epoch = some word)
    (hi : findNonMaximumCoordinate word = some i)
    (hepoch : let (epoch, _, _) := out.forgery; guessedEpoch guess = epoch)
    (hchain : guessedChain guess = i)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    let (epoch, _, signature) := out.forgery
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (P.chain pp epoch i (word i)
        (2 ^ w - 2 - (word i).val) (signature.ots i))) = response := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hepoch
  let out : Result PP H M R h v := ⟨pk, sk, (epoch, message, signature), history⟩
  obtain ⟨hseed, hendpoints⟩ := runContextSpliced_support_keys P enc K
    (intervalChainContext P I fillers) A pp guess response starts out hout
  have hrem := hwin
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hrem
  have hendpoint := intervalChainRemainder_endpoint_eq_forged P enc K I fillers out word
    hword hrem.1 i
  dsimp only [out] at hendpoint
  rw [hseed] at hendpoint
  have hselected : sk.endpoints epoch i = response := by
    rw [hendpoints, ← hepoch, ← hchain]
    exact splicedEndpoints_guess_final P pp guess response starts hfinal
  rw [hselected] at hendpoint
  have hsmall := findNonMaximumCoordinate_sound word hi
  have heval := chainFinalPredecessor_sound P pp epoch i (word i)
    (guessedPosition guess) (signature.ots i) response hsmall hfinal hendpoint.symm
  simpa only [hepoch, hchain] using heval

private theorem extractChainPreimage_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true) :
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (extractChainPreimage P enc K I fillers guess starts out)) = response := by
  obtain ⟨hseed, _⟩ := runContextSpliced_support_keys P enc K (intervalChainContext P I fillers)
    A pp guess response starts out hout
  have hrem := hwin
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hrem
  rcases hrem with ⟨hrem, hsel⟩
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  unfold intervalSelectedCut at hsel
  dsimp only at hsel
  rw [hseed] at hsel
  cases hentry : history epoch with
  | none =>
      cases hword : enc.value pp message signature.randomizer epoch with
      | none => simp [hentry, hword] at hsel
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [hentry, hword, hi] at hsel
        | some i =>
          have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
              (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
            simpa [hentry, hword, hi] using hsel
          rcases hs with ⟨hepoch, hchain, hfinal⟩
          have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
            (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
            word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
          simp only [extractChainPreimage, extractChainPreimageWithFallback, hwin,
            Bool.true_eq_false, ite_false, hentry]
          rw [hseed, hword]
          simp only [hi]
          exact heval
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
        cases hword : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hword] at hsel
        | some word =>
          cases hi : findNonMaximumCoordinate word with
          | none => simp [hentry, hword, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
              simpa [hentry, hword, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hfinal⟩
            have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
              word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
            simp only [extractChainPreimage, extractChainPreimageWithFallback, hwin,
            Bool.true_eq_false, ite_false, hentry]
            rw [hseed, hword]
            simp only [hi]
            exact heval
    | some honest =>
      cases hhonest : enc.value pp first honest.randomizer epoch with
      | none => simp [hentry, hhonest] at hsel
      | some honestWord =>
        cases hforged : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hhonest, hforged] at hsel
        | some forgedWord =>
          cases hi : GXMSS.Security.findSmallerCoordinate honestWord forgedWord with
          | none => simp [hentry, hhonest, hforged, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = (honestWord i).val := by
              simpa [hentry, hhonest, hforged, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hposition⟩
            obtain ⟨wr, hsig, hwr⟩ := runContextSpliced_successful_record_signature P enc K
              (intervalChainContext P I fillers) A pp guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v)
              hout epoch first honest hentry
            have hr : honest.randomizer = wr.2 := by rw [hsig]; rfl
            have hwordEq : wr.1 = honestWord := by
              have hh := hhonest
              rw [hr, hwr] at hh
              exact Option.some.inj hh
            have hsigAnswer : honest.ots i = response := by
              rw [hsig, ← hchain]
              apply contextSplicedSignatureOfWord_guess_succ P (intervalChainContext P I fillers)
                pp guess response starts (splicedEndpoints P pp guess response starts) epoch wr
                hepoch.symm
              rw [hwordEq, hchain]
              exact hposition.symm
            simp only [intervalChainRemainderObservation, Bool.and_eq_true] at hrem
            rcases hrem with ⟨_, hcut⟩
            simp only [designatedCutHolds, forgedEpochSource, hentry] at hcut
            rw [hseed] at hcut
            simp only [hhonest, hforged, hi] at hcut
            have hcutEq := of_decide_eq_true hcut
            have hsmaller := GXMSS.Security.findSmallerCoordinate_sound honestWord forgedWord hi
            obtain ⟨preimage, hfind, heval⟩ := chainCutPredecessor_sound P pp epoch i
              (forgedWord i) (honestWord i) (guessedPosition guess) (honest.ots i) (signature.ots i)
              hsmaller hposition hcutEq
            have heval' : TweakableHash.eval P.thf pp (P.chainTweak
                (guessedEpoch guess, guessedChain guess, guessedPosition guess))
                (P.digestInput preimage) = response := by
              simpa only [hepoch, hchain, hsigAnswer] using heval
            simp only [extractChainPreimage, extractChainPreimageWithFallback, hwin,
            Bool.true_eq_false, ite_false, hentry]
            rw [hseed, hhonest, hforged]
            simp only [hi, hfind]
            exact heval'

private theorem extractChainPreimageWithFallback_sound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (fillers : Fillers I H)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H) (fallback : H)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts))
    (hwin : intervalSelectedChainObservation P enc K I fillers guess out = true) :
    TweakableHash.eval P.thf pp (P.chainTweak
      (guessedEpoch guess, guessedChain guess, guessedPosition guess))
      (P.digestInput (
        extractChainPreimageWithFallback P enc K I fillers guess fallback out)) = response := by
  obtain ⟨hseed, _⟩ := runContextSpliced_support_keys P enc K (intervalChainContext P I fillers)
    A pp guess response starts out hout
  have hrem := hwin
  simp only [intervalSelectedChainObservation, Bool.and_eq_true] at hrem
  rcases hrem with ⟨hrem, hsel⟩
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  unfold intervalSelectedCut at hsel
  dsimp only at hsel
  rw [hseed] at hsel
  cases hentry : history epoch with
  | none =>
      cases hword : enc.value pp message signature.randomizer epoch with
      | none => simp [hentry, hword] at hsel
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [hentry, hword, hi] at hsel
        | some i =>
          have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
              (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
            simpa [hentry, hword, hi] using hsel
          rcases hs with ⟨hepoch, hchain, hfinal⟩
          have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
            (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
            word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
          simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
          rw [hseed, hword]
          simp only [hi]
          exact heval
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
        cases hword : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hword] at hsel
        | some word =>
          cases hi : findNonMaximumCoordinate word with
          | none => simp [hentry, hword, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
              simpa [hentry, hword, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hfinal⟩
            have heval := intervalFinalPreimage_sound P enc K I A pp fillers guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v) hout hwin
              word i (by dsimp only; rw [hseed]; exact hword) hi hepoch hchain hfinal
            simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
            rw [hseed, hword]
            simp only [hi]
            exact heval
    | some honest =>
      cases hhonest : enc.value pp first honest.randomizer epoch with
      | none => simp [hentry, hhonest] at hsel
      | some honestWord =>
        cases hforged : enc.value pp message signature.randomizer epoch with
        | none => simp [hentry, hhonest, hforged] at hsel
        | some forgedWord =>
          cases hi : GXMSS.Security.findSmallerCoordinate honestWord forgedWord with
          | none => simp [hentry, hhonest, hforged, hi] at hsel
          | some i =>
            have hs : guessedEpoch guess = epoch ∧ guessedChain guess = i ∧
                (guessedPosition guess).val + 1 = (honestWord i).val := by
              simpa [hentry, hhonest, hforged, hi] using hsel
            rcases hs with ⟨hepoch, hchain, hposition⟩
            obtain ⟨wr, hsig, hwr⟩ := runContextSpliced_successful_record_signature P enc K
              (intervalChainContext P I fillers) A pp guess response starts
              (⟨pk, sk, (epoch, message, signature), history⟩ : Result PP H M R h v)
              hout epoch first honest hentry
            have hr : honest.randomizer = wr.2 := by rw [hsig]; rfl
            have hwordEq : wr.1 = honestWord := by
              have hh := hhonest
              rw [hr, hwr] at hh
              exact Option.some.inj hh
            have hsigAnswer : honest.ots i = response := by
              rw [hsig, ← hchain]
              apply contextSplicedSignatureOfWord_guess_succ P (intervalChainContext P I fillers)
                pp guess response starts (splicedEndpoints P pp guess response starts) epoch wr
                hepoch.symm
              rw [hwordEq, hchain]
              exact hposition.symm
            simp only [intervalChainRemainderObservation, Bool.and_eq_true] at hrem
            rcases hrem with ⟨_, hcut⟩
            simp only [designatedCutHolds, forgedEpochSource, hentry] at hcut
            rw [hseed] at hcut
            simp only [hhonest, hforged, hi] at hcut
            have hcutEq := of_decide_eq_true hcut
            have hsmaller := GXMSS.Security.findSmallerCoordinate_sound honestWord forgedWord hi
            obtain ⟨preimage, hfind, heval⟩ := chainCutPredecessor_sound P pp epoch i
              (forgedWord i) (honestWord i) (guessedPosition guess) (honest.ots i) (signature.ots i)
              hsmaller hposition hcutEq
            have heval' : TweakableHash.eval P.thf pp (P.chainTweak
                (guessedEpoch guess, guessedChain guess, guessedPosition guess))
                (P.digestInput preimage) = response := by
              simpa only [hepoch, hchain, hsigAnswer] using heval
            simp only [extractChainPreimageWithFallback, hwin, Bool.true_eq_false,
            ite_false, hentry]
            rw [hseed, hhonest, hforged]
            simp only [hi, hfind]
            exact heval'

private noncomputable def chainPRESelectedProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    pure (intervalSelectedChainObservation P enc K I fillers guess out)

private noncomputable def chainPREFilteredProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def chainTerminalBackProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let response := P.chain pp (guessedEpoch guess) (guessedChain guess)
      (guessedPosition guess).val 1 hidden
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def chainPREExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    let preimage := extractChainPreimage P enc K I fillers guess starts out
    pure (decide (TweakableHash.eval P.thf pp tweak
      (P.digestInput preimage) = response))

private theorem chainPREOracles_liftComp
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (pp : PP) {S : Type}
    (oa : ProbComp S) (state : SM_DT_PRE_State T H) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem P) pp)
      (OracleComp.liftComp oa _)).run state = (fun x => (x, state)) <$> oa := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem chainPREOracles_challenge
    [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (pp : PP) (t : T) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem P) pp)
      (liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
        collectionSpec (chainPREProblem P).thColl)).query (.inr (.inl t))))).run
      (([], []) : SM_DT_PRE_State T H) =
      (fun hidden => (some (TweakableHash.eval P.thf pp t (P.digestInput hidden)),
        ([(t, hidden)], []))) <$> ($ᵗ H) := by
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_query_right, QueryImpl.add_apply_inl]
  simp [SM_DT_PRE_challengeOracle, TweakFresh, TweakReserved, chainPREProblem,
    SM_DT_PRE_Problem.standalone, StateT.run_bind, map_eq_bind_pure_comp]

private theorem chainPREExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Experiment (selectedChainPreimageReduction P enc K I hv hw A) =
      chainPREExplicitProgram P enc K I A := by
  unfold SM_DT_PRE_Experiment selectedChainPreimageReduction chainPREExplicitProgram chainPREPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainPREOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainPREOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The terminal selected experiment has one active target and one fixed private filler table.
Hidden inputs are uniform on the original digest subspace. -/
noncomputable def selectedPreimageExperiment
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
  exact chainPRESelectedProgram P enc K I A

/-- The terminal selected mass is charged to the actual original-domain one-target PRE adversary.
The witness proof uses only chain recurrence, the concrete designated cut and native history. -/
theorem selectedPreimageMass_le_advantage
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} ≤
      SM_DT_PRE_Advantage (selectedChainPreimageReduction P enc K I hv hw A) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  change 𝒟[chainPRESelectedProgram P enc K I A] {true} ≤ _
  unfold SM_DT_PRE_Advantage
  rw [chainPREExperiment_eq_explicit P enc K I hv hw A]
  unfold chainPRESelectedProgram chainPREExplicitProgram
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
  · have heval := extractChainPreimage_sound P enc K I A pp fillers guess
      (TweakableHash.eval P.thf pp
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (P.digestInput hidden))
      starts out hout hselected
    have hwin := heval
    simp only [show activeGuess I selector = guess from rfl, hselected, hwin,
      decide_true, evalDist_pure,
      MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton true)]
    simp
  · have hfalse := Bool.eq_false_iff.mpr hselected
    simp [show activeGuess I selector = guess from rfl, hfalse]

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

private noncomputable def jointZeroRealProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let zero : Guess h w v := (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) 0)
  let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
    zero (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
  pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def jointTerminalProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let response := P.chain pp (guessedEpoch guess) (guessedChain guess)
    (guessedPosition guess).val 1 x
  let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
    A pp guess guess response starts
  pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))

private noncomputable def jointUDFrontProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) : ProbComp Bool := do
  let (pp, guess, fillers) ← jointOuterDraw P I
  let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let response := match world with
    | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
    | .ideal => x
  if hybrid.val < (guessedPosition guess).val then
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
      (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) hybrid.val) response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
  else pure false

private theorem joint_native_returned_mass_telescope
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram P enc K I A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) * 𝒟[jointUDFrontProgram P enc K I A .ideal] {true} =
      𝒟[jointTerminalProgram P enc K I A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) * 𝒟[jointUDFrontProgram P enc K I A .real] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  let : MeasurableSpace (PP × Guess h w v × Fillers I H) := ⊤
  unfold jointZeroRealProgram jointTerminalProgram jointUDFrontProgram
  apply bind_true_mass_telescope (jointOuterDraw P I)
  intro z
  rcases z with ⟨pp, guess, fillers⟩
  exact context_fixed_selector_returned_measure_telescope P enc K
    (intervalChainContext P I fillers) A pp guess
    (intervalSelectedChainObservation P enc K I fillers guess)

private theorem chainUDChainCut_mass_eq_front
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    𝒟[chainUDChainCutProgram P enc K I A world] {true} =
      𝒟[jointUDFrontProgram P enc K I A world] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainUDChainCutProgram jointUDFrontProgram jointOuterDraw
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  let guess := activeGuess I selector
  let F : Fin (2 ^ w - 1) → (Epoch h → Fin v → H) → Fillers I H → ProbComp Bool :=
    fun hybrid starts fillers => do
      let x ← ($ᵗ H : ProbComp H)
      let response := match world with
        | .real => P.chain pp (guessedEpoch guess) (guessedChain guess) hybrid.val 1 x
        | .ideal => x
      if hybrid.val < (guessedPosition guess).val then
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess (guessedEpoch guess, guessedChain guess, hybrid) response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
      else pure false
  have hswap : 𝒟[do
      let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      F hybrid starts fillers] =
      𝒟[do
        let fillers ← sampleFillers I H
        let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
        let starts ← GXMSS.sampleStarts H h v
        F hybrid starts fillers] := by
    calc
      _ = 𝒟[do
        let hybrid ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp (Fin (2 ^ w - 1)))
        let fillers ← sampleFillers I H
        let starts ← GXMSS.sampleStarts H h v
        F hybrid starts fillers] := by
          apply evalDist_bind_congr_of_support
          intro hybrid _
          exact evalDist_bind_bind_swap _ _ (fun starts fillers => F hybrid starts fillers)
      _ = _ := evalDist_bind_bind_swap _ _
        (fun hybrid fillers => GXMSS.sampleStarts H h v >>= fun starts => F hybrid starts fillers)
  have hfin (j : Fin (2 ^ w - 1)) : Fin.ofNat (2 ^ w - 1) j.val = j := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.isLt
  simpa only [F, guess, hfin] using congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hswap

private theorem chainPRESelected_mass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainPRESelectedProgram P enc K I A] {true} =
      𝒟[chainPREFilteredProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainPRESelectedProgram chainPREFilteredProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro fillers
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro hidden
  let guess := activeGuess I selector
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess guess
      (TweakableHash.eval P.thf pp
        (P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess))
          (P.digestInput hidden))
        starts

private theorem chainPREFiltered_mass_eq_terminalBack
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainPREFilteredProgram P enc K I A] {true} =
      𝒟[chainTerminalBackProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainPREFilteredProgram chainTerminalBackProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro fillers
  let guess := activeGuess I selector
  let continuation : H → ProbComp Bool := fun response => do
    let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
      A pp guess guess response starts
    pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))
  have hprojection := chainUD_real_response_bind_chain P pp (guessedEpoch guess)
    (guessedChain guess) (guessedPosition guess) continuation
  simpa only [SM_DT_UD_response, chainUDProblem, SM_DT_UD_Problem.standalone,
    id_eq, continuation, guess, bind_assoc, pure_bind] using
    congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hprojection

private theorem chainTerminalBack_mass_eq_front
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainTerminalBackProgram P enc K I A] {true} =
      𝒟[jointTerminalProgram P enc K I A] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  let : MeasurableSpace (Fillers I H) := ⊤
  unfold chainTerminalBackProgram jointTerminalProgram jointOuterDraw
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro selector
  exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
    (evalDist_bind_bind_swap (GXMSS.sampleStarts H h v) (sampleFillers I H) _)

/-- The filtered first-cut experiment samples an independent real challenge input, one active
selector and a fixed filler table. The observation retains returned false and unreturned mass. -/
private noncomputable def zeroRealFilteredExperiment
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
  exact jointZeroRealProgram P enc K I A

/-- Exact native additive form of the signed joint chain telescope, before absolute values.
The same one-target original-domain UD adversary appears in both worlds and the terminal term is the
actual original-domain PRE selected experiment; all cuts retain the same sampled filler table. -/
private theorem selectedChain_native_telescope
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[zeroRealFilteredExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .ideal (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .real (chainUndetectabilityReduction P enc K I hv hw A)]
            {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  change 𝒟[jointZeroRealProgram P enc K I A] {true} + _ =
    𝒟[chainPRESelectedProgram P enc K I A] {true} + _
  rw [chainUDExperiment_true_eq_chainCut, chainUDExperiment_true_eq_chainCut,
    chainUDChainCut_mass_eq_front, chainUDChainCut_mass_eq_front,
    chainPRESelected_mass_eq_filtered, chainPREFiltered_mass_eq_terminalBack,
    chainTerminalBack_mass_eq_front]
  exact joint_native_returned_mass_telescope P enc K I A

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

private theorem fixedSelectedSource_mass_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (fillers : Fillers I H) :
    𝒟[fixedSelectedSourceProgram P enc K I A pp guess fillers] {true} =
      𝒟[do
        let starts ← GXMSS.sampleStarts H h v
        let x ← ($ᵗ H : ProbComp H)
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp guess
          (guessedEpoch guess, guessedChain guess, Fin.ofNat (2 ^ w - 1) 0)
          (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne _)
  let zero : Guess h w v := (guessedEpoch guess, guessedChain guess, ⟨0, hn⟩)
  let source : ProbComp Bool := do
    let starts ← GXMSS.sampleStarts H h v
    let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0
      ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    pure (intervalSelectedChainObservation P enc K I fillers guess out)
  have hsource : fixedSelectedSourceProgram P enc K I A pp guess fillers = source := by
    unfold fixedSelectedSourceProgram source
    apply bind_congr
    intro starts
    dsimp only
    rw [runContextSpliced_honest_interval]
    simp only [bind_assoc]
    apply bind_congr
    rintro ⟨publicKey, forgery, history⟩
    rfl
  have hpoint (starts : Epoch h → Fin v → H) :
      𝒟[do
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0
          ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
          A pp guess response starts
        pure (intervalSelectedChainObservation P enc K I fillers guess out)] {true} =
      𝒟[do
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
          (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess zero response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
    have hfilter := intervalSelectedSplice_mass_eq_filtered P enc K I A pp fillers guess guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess))) starts
    have hcut := runContextFilteredSpliced_honest_from_zero P enc K
      (intervalChainContext P I fillers) A pp guess starts hn
    rw [← hcut] at hfilter
    simpa only [zero, map_eq_bind_pure_comp, Function.comp_def] using hfilter
  have hzero : (guessedPosition zero).val = 0 := rfl
  have hresample := intervalSelectedSplice_zero_real_resampling P enc K I A pp fillers
    guess zero hzero hn rfl rfl
  have hmass : 𝒟[source] {true} =
      𝒟[do
        let starts ← GXMSS.sampleStarts H h v
        let response := P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
          (starts (guessedEpoch guess) (guessedChain guess))
        let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
          A pp guess zero response starts
        pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess))]
        {true} := by
    unfold source
    apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
    exact hpoint
  rw [hsource, hmass]
  have hswap := OracleComp.evalDist_bind_bind_swap ($ᵗ H : ProbComp H) (GXMSS.sampleStarts H h v)
    (fun x starts => do
      let out ← runContextFilteredSpliced P enc K (intervalChainContext P I fillers)
        A pp guess zero (P.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x) starts
      pure (out.elim false (intervalSelectedChainObservation P enc K I fillers guess)))
  have hzeroFin : (⟨0, hn⟩ : Fin (2 ^ w - 1)) = Fin.ofNat (2 ^ w - 1) 0 := by
    apply Fin.ext
    simp
  exact hresample.trans (by
    simpa only [zero, guessedEpoch, guessedChain, hzeroFin] using
      congrArg (fun d : MeasureTheory.Measure Bool => d {true}) hswap)

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

private theorem selectedSource_mass_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} =
      𝒟[zeroRealFilteredExperiment P enc K I hv hw A] {true} := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  let : MeasurableSpace (PP × Guess h w v × Fillers I H) := ⊤
  unfold selectedSourceExperiment zeroRealFilteredExperiment jointZeroRealProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro z
  rcases z with ⟨pp, guess, fillers⟩
  exact fixedSelectedSource_mass_eq_zeroReal P enc K I A pp guess fillers

/-- Native signed chain identity for the actual selected interval source event. The exact
real-minus-ideal UD contribution is retained before taking any absolute value. -/
theorem selectedSource_native_telescope
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[selectedSourceExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .ideal (chainUndetectabilityReduction P enc K I hv hw A)] {true} =
      𝒟[selectedPreimageExperiment P enc K I hv hw A] {true} +
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[SM_DT_UD_Experiment .real (chainUndetectabilityReduction P enc K I hv hw A)]
            {true} := by
  rw [selectedSource_mass_eq_zeroReal]
  exact selectedChain_native_telescope P enc K I hv hw A

/-- One-target chain PRE with fixed `starts 0 0` fallback. The selected-coordinate
public strategy remains separate; unselected fallback outputs can accidentally win. -/
noncomputable def chainPreimageReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Adversary (chainPREProblem P) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  exact {
    State := ChainPREState H h w v I
    choose := chainPREPick P I
    invert state pp := do
      let guess := activeGuess I state.selector
      let starts := state.starts
      let fallback := starts 0 0
      match state.answer with
      | none => return (0, fallback)
      | some response =>
        let out ← runContextSpliced P enc K (intervalChainContext P I state.fillers)
          A pp guess response state.starts
        let preimage := extractChainPreimageWithFallback P enc K I state.fillers guess fallback out
        return (0, preimage) }

private noncomputable def fixedFallbackPREExplicitProgram
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := by
  letI : NeZero (I.last.val - I.first.val + 1) := ⟨by omega⟩
  exact do
    let thf := P.thf
    let pp ← thf.seedGen
    let selector ← ($ᵗ (ActiveSelector I w v) : ProbComp (ActiveSelector I w v))
    let starts ← GXMSS.sampleStarts H h v
    let fillers ← sampleFillers I H
    let hidden ← ($ᵗ H : ProbComp H)
    let guess := activeGuess I selector
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let response := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runContextSpliced P enc K (intervalChainContext P I fillers)
      A pp guess response starts
    let fallback := starts 0 0
    let preimage :=
      extractChainPreimageWithFallback P enc K I fillers guess fallback out
    pure (decide (TweakableHash.eval P.thf pp tweak
      (P.digestInput preimage) = response))

private theorem fixedFallbackPREExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Experiment (chainPreimageReduction P enc K I hv hw A) =
      fixedFallbackPREExplicitProgram P enc K I A := by
  unfold SM_DT_PRE_Experiment chainPreimageReduction
    fixedFallbackPREExplicitProgram chainPREPick
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [chainPREOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [chainPREOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

end GXMSS.Interval.Reductions.Chain

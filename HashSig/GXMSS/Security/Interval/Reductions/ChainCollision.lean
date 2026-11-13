/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleGames
public import HashSig.GXMSS.Security.Reductions.TargetRegistration.Tweaks
import all HashSig.GXMSS.Security.Interval.Reductions.ChainPrograms
import HashSig.GXMSS.Security.Interval.Reductions.EncodingSimulation
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
-- The partition proof uses the private retained-key source program.
import all HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import HashSig.GXMSS.Security.Reductions.TargetRegistration.Basic
import all HashSig.GXMSS.Security.Reductions.TargetRegistration.Chains
import VCVio.OracleComp.EvalDist.Sum

/-!
# Native interval encoding and chain collision bounds

Honest chain targets are registered before revealing the actual public seed. A fixed filler table
is retained through the real interval interaction. The native collision observations preserve full
signatures, failed and consumed history, exact freshness and incidental fallback outcomes.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Standalone chain target-collision problem with the complete positive-step capacity. -/
@[expose] def chainTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))

/-- The chain problem has room for all positive steps of all honest chains, including `w = 0`. -/
theorem chainProblem_capacity (hash : HashInstance PP T X H h w v) :
    (2 ^ h) * v * (2 ^ w - 1) ≤ (chainTCRProblem hash).numTargets := by
  change (2 ^ h) * v * (2 ^ w - 1) ≤ (2 ^ h) * v * 2 ^ w
  exact Nat.mul_le_mul_left ((2 ^ h) * v) (Nat.sub_le _ _)

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions.Chain
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
  GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.IntervalMerkle SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Register all honest chain targets for either chain-collision reduction. -/
private def tcrChainSetup [SampleableType H]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
      collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl))
      (TCRKeyState PP T X H h v) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
  let (endpoints, registered) ← (tcrEndpoints hash targets starts fallback).run []
  return ⟨starts, endpoints, fallback, registered, fallback⟩

/-- The chain reductions' honest setup samples the accepted starts, reconstructs the ordinary
endpoint family, and exposes exactly the positive-step registration history. -/
private theorem tcrChainSetup_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H h w v) (targets : ℕ) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) ≤ targets) :
    (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (tcrChainSetup hash targets)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        let endpoints := GXMSS.endpoints hash pp starts
        let registered := endpointTargets hash pp starts
        pure ((⟨starts, endpoints, fallback, registered, fallback⟩ :
          TCRKeyState PP T X H h v), registered, [])) := by
  have hunif {A : Type} (oa : ProbComp A) (state : SM_DT_TCR_State T X) :
      (simulateQ
        (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
        (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
    rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
      simulateQ_ofLift_eq_self]
    simp
  simp only [tcrChainSetup, simulateQ_bind, StateT.run_bind]
  rw [hunif, bind_map_left]
  apply bind_congr
  intro fallback
  rw [hunif, bind_map_left]
  apply bind_congr
  intro starts
  rw [tcrEndpoints_run_empty hash targets pp starts fallback hcap]
  simp

/-- Every positive paper step of every honest chain occurs in the all-epoch endpoint traversal. -/
private theorem chainTarget_mem_endpointTargets (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Epoch h → Fin v → H) (ep : Epoch h) (i : Fin v)
    (j : Fin (2 ^ w - 1)) :
    (hash.chainTweak (ep, i, ⟨j.val, by omega⟩),
      hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i))) ∈
      endpointTargets hash pp starts := by
  simp only [endpointTargets, List.mem_flatten, List.mem_ofFn]
  refine ⟨(List.ofFn fun i : Fin v =>
    chainTargets hash pp ep i (starts ep i) (2 ^ w - 1) (by omega)).flatten, ?_, ?_⟩
  · exact ⟨ep, rfl⟩
  · simp only [List.mem_flatten, List.mem_ofFn]
    refine ⟨chainTargets hash pp ep i (starts ep i) (2 ^ w - 1) (by omega), ⟨i, rfl⟩, ?_⟩
    simp [chainTargets]

/-- The exact candidate returned by the fixed first-chain reduction after source interaction. -/
private def firstChainCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : GXMSS.Reductions.TCRKeyState PP T X H h v) (pp : PP)
    (out : GXMSS.Reductions.Result PP H M R h v) : ℕ × X :=
  let fallback := (0, hash.digestInput state.fallback)
  let epoch := out.forgery.1
  let forgedMessage := out.forgery.2.1
  let forgedSignature := out.forgery.2.2
  match out.history epoch with
  | some (msg, some signature) =>
    match enc.value pp msg signature.randomizer epoch,
      enc.value pp forgedMessage forgedSignature.randomizer epoch with
    | some honestWord, some forgedWord =>
      if honestWord = forgedWord then
        match (Fin.find? fun j => decide (signature.ots j ≠ forgedSignature.ots j)) with
        | none => fallback
        | some i =>
          match hash.findChainCollision pp epoch i (honestWord i)
              (2 ^ w - 1 - (honestWord i).val) (signature.ots i)
              (forgedSignature.ots i) with
          | none => fallback
          | some d =>
            let tweak := hash.chainTweak (epoch, i,
              ⟨(honestWord i).val + d.val, by omega⟩)
            let first := hash.digestInput
              (hash.chain pp epoch i (honestWord i) d (signature.ots i))
            let second := hash.digestInput
              (hash.chain pp epoch i (honestWord i) d (forgedSignature.ots i))
            (GXMSS.Reductions.registeredIndex state.targets tweak first, second)
      else fallback
    | _, _ => fallback
  | _ => fallback

private def firstChainCandidateWins [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (history : List (T × X)) (candidate : ℕ × X) : Bool :=
  match history[candidate.1]? with
  | none => false
  | some (t, first) =>
    decide (candidate.2 ≠ first ∧
      (HashInstance.thf hash).eval pp t candidate.2 =
        (HashInstance.thf hash).eval pp t first)

/-- The first unequal OTS coordinate yields a registered honest-first collision target. -/
private theorem firstChain_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h))
    (word : Codeword v (2 ^ w)) (honestOTS forgedOTS : Fin v → H)
    (hhonest : ∀ i, honestOTS i =
      hash.chain pp ep i 0 (word i) (starts ep i))
    (hend : ∀ i, hash.chain pp ep i (word i)
      (2 ^ w - 1 - (word i).val) (honestOTS i) =
        hash.chain pp ep i (word i)
          (2 ^ w - 1 - (word i).val) (forgedOTS i))
    (hne : honestOTS ≠ forgedOTS) :
    ∃ i : Fin v, ∃ d : Fin (2 ^ w - 1 - (word i).val),
      (Fin.find? fun j => decide (honestOTS j ≠ forgedOTS j)) = some i ∧
      hash.findChainCollision pp ep i (word i)
        (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i) = some d ∧
      let tweak := hash.chainTweak (ep, i, ⟨(word i).val + d.val, by omega⟩)
      let first := hash.digestInput (hash.chain pp ep i (word i) d (honestOTS i))
      let second := hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i))
      firstChainCandidateWins hash pp (GXMSS.Reductions.endpointTargets hash pp starts)
        (GXMSS.Reductions.registeredIndex
          (GXMSS.Reductions.endpointTargets hash pp starts) tweak first, second) = true := by
  obtain ⟨different, hdifferent⟩ := Function.ne_iff.mp hne
  have hisome := Fin.isSome_find?_of_eq_true
    (p := fun j => decide (honestOTS j ≠ forgedOTS j))
    (i := different) (decide_eq_true hdifferent)
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisome
  have hcoord := of_decide_eq_true (Fin.eq_true_of_find?_eq_some hi)
  have hdSome := hash.findChainCollision_isSome pp ep i (word i)
    (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i) hcoord (hend i)
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hdSome
  refine ⟨i, d, hi, hd, ?_⟩
  let j : Fin (2 ^ w - 1) := ⟨(word i).val + d.val, by omega⟩
  have hprefix : hash.chain pp ep i (word i) d (honestOTS i) =
      hash.chain pp ep i 0 j.val (starts ep i) := by
    rw [hhonest i]
    simpa [j] using (hash.chain_add pp ep i 0 (word i).val d.val (starts ep i)).symm
  have hsound := hash.findChainCollision_hash_sound pp ep i (word i)
    (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i)
    (by omega) hd
  dsimp only [GXMSS.Security.HashCollision.Sound] at hsound
  rw [hprefix] at hsound
  have hlookup := registeredIndex_lookup_of_mem (endpointTargets hash pp starts) _ _
    (chainTarget_mem_endpointTargets hash pp starts ep i j)
  dsimp [firstChainCandidateWins]
  rw [hprefix]
  simpa [j, hlookup, GXMSS.Security.HashCollision.Sound] using
    (show decide
      (hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i)) ≠
        hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)) ∧
       hash.thf.eval pp (hash.chainTweak (ep, i, j))
         (hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i))) =
       hash.thf.eval pp (hash.chainTweak (ep, i, j))
         (hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)))) = true from
      decide_eq_true ⟨hsound.1.symm, hsound.2.symm⟩)

/-- Exact candidate returned by the fixed second-chain reduction after source interaction. -/
private def secondChainCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : GXMSS.Reductions.TCRKeyState PP T X H h v) (pp : PP)
    (out : GXMSS.Reductions.Result PP H M R h v) : ℕ × X :=
  let fallback := (0, hash.digestInput state.fallback)
  let ep := out.forgery.1
  let forgedMessage := out.forgery.2.1
  let forgedSignature := out.forgery.2.2
  match out.history ep with
  | some (msg, some signature) =>
    match enc.value pp msg signature.randomizer ep,
      enc.value pp forgedMessage forgedSignature.randomizer ep with
    | some honestWord, some forgedWord =>
      match (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
      | none => fallback
      | some i =>
        match hash.findChainCut pp ep i (forgedWord i) (honestWord i)
            (2 ^ w - 1) (signature.ots i) (forgedSignature.ots i) with
        | some (.inr d) =>
          let advanced := hash.chain pp ep i (forgedWord i)
            ((honestWord i).val - (forgedWord i).val) (forgedSignature.ots i)
          let tweak := hash.chainTweak (ep, i,
            ⟨(honestWord i).val + d.val, by omega⟩)
          let first := hash.digestInput
            (hash.chain pp ep i (honestWord i) d (signature.ots i))
          let second := hash.digestInput
            (hash.chain pp ep i (honestWord i) d advanced)
          (GXMSS.Reductions.registeredIndex state.targets tweak first, second)
        | _ => fallback
    | _, _ => fallback
  | _ => fallback

/-- A non-aligned designated cut supplies a registered honest-first target collision. -/
private theorem secondChain_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h))
    (honestWord forgedWord : Codeword v (2 ^ w))
    (honestOTS forgedOTS : Fin v → H) (i : Fin v)
    (hi : (Fin.find? fun j => decide (forgedWord j < honestWord j)) = some i)
    (hhonest : honestOTS i = hash.chain pp ep i 0 (honestWord i) (starts ep i))
    (hend : hash.chain pp ep i (honestWord i)
      (2 ^ w - 1 - (honestWord i).val) (honestOTS i) =
        hash.chain pp ep i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i))
    (hneCut : hash.chain pp ep i (forgedWord i)
      ((honestWord i).val - (forgedWord i).val) (forgedOTS i) ≠ honestOTS i) :
    ∃ d : Fin (2 ^ w - 1 - (honestWord i).val),
      hash.findChainCut pp ep i (forgedWord i) (honestWord i)
        (2 ^ w - 1) (honestOTS i) (forgedOTS i) = some (.inr d) ∧
      let advanced := hash.chain pp ep i (forgedWord i)
        ((honestWord i).val - (forgedWord i).val) (forgedOTS i)
      let tweak := hash.chainTweak (ep, i, ⟨(honestWord i).val + d.val, by omega⟩)
      let first := hash.digestInput (hash.chain pp ep i (honestWord i) d (honestOTS i))
      let second := hash.digestInput (hash.chain pp ep i (honestWord i) d advanced)
      firstChainCandidateWins hash pp (GXMSS.Reductions.endpointTargets hash pp starts)
        (GXMSS.Reductions.registeredIndex
          (GXMSS.Reductions.endpointTargets hash pp starts) tweak first, second) = true := by
  have hsome := hash.findChainCut_isSome_of_smallerCoordinate pp ep honestWord forgedWord
    (by simpa only [Fin.lt_def] using hi) (honestOTS i) (forgedOTS i) hend
  obtain ⟨cut, hcut⟩ := Option.isSome_iff_exists.mp hsome
  cases cut with
  | inl u =>
    rw [HashInstance.findChainCut_eq] at hcut
    split at hcut
    next heq => exact False.elim (hneCut heq)
    next => simp at hcut
  | inr d =>
    refine ⟨d, hcut, ?_⟩
    let j : Fin (2 ^ w - 1) := ⟨(honestWord i).val + d.val, by omega⟩
    have hprefix : hash.chain pp ep i (honestWord i) d (honestOTS i) =
        hash.chain pp ep i 0 j.val (starts ep i) := by
      rw [hhonest]
      simpa [j] using
        (hash.chain_add pp ep i 0 (honestWord i).val d.val (starts ep i)).symm
    have hsound := hash.findChainCut_hash_sound pp ep i (forgedWord i)
      (honestWord i) (2 ^ w - 1) (honestOTS i) (forgedOTS i)
      (by omega) (by omega) hcut
    dsimp only [GXMSS.Security.HashCollision.Sound] at hsound
    rw [hprefix] at hsound
    have hlookup := registeredIndex_lookup_of_mem (endpointTargets hash pp starts) _ _
      (chainTarget_mem_endpointTargets hash pp starts ep i j)
    dsimp [firstChainCandidateWins]
    rw [hprefix]
    simpa [j, hlookup, GXMSS.Security.HashCollision.Sound] using
      (show decide
        (hash.digestInput (hash.chain pp ep i (honestWord i) d
            (hash.chain pp ep i (forgedWord i)
              ((honestWord i).val - (forgedWord i).val) (forgedOTS i))) ≠
          hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)) ∧
         hash.thf.eval pp (hash.chainTweak (ep, i, j))
           (hash.digestInput (hash.chain pp ep i (honestWord i) d
             (hash.chain pp ep i (forgedWord i)
               ((honestWord i).val - (forgedWord i).val) (forgedOTS i)))) =
         hash.thf.eval pp (hash.chainTweak (ep, i, j))
           (hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)))) = true from
        decide_eq_true ⟨hsound.1.symm, hsound.2.symm⟩)

/-- Encoding collision experiment in the interval source signing interaction. -/
noncomputable def encodingCollisionExperiment
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (intervalEncodingCollision enc I out)

/-- The encoding collision mass is bounded by `encodingTargetCollisionReduction`.
The pathwise budget counts failed, repeated and inactive signing requests. -/
theorem encodingCollisionMass_le_advantage
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v)
    (hbound : SigningQueryBound qs A) :
    ProbCompRuntime.probComp.evalDist (encodingCollisionExperiment P enc K I A) {true} ≤
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) := by
  exact intervalEncodingCollisionMass_le_advantage P enc qs K I A hbound

private structure ChainState (PP T X H : Type) (h v : ℕ) (I : Interval h) where
  complete : TCRKeyState PP T X H h v
  fillers : Fillers I H

private noncomputable def chainSetup [SampleableType H]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T X H +
      collectionSpec (SM_DT_TCR_Problem.standalone P.thf targets).thColl))
      (ChainState PP T X H h v I) := do
  let complete ← tcrChainSetup P targets
  let fillers ← OracleComp.liftComp (sampleFillers I H) _
  return ⟨complete, fillers⟩

private theorem chainSetup_run [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (targets : ℕ) (I : Interval h) (pp : PP)
    (hcap : (2 ^ h) * v * (2 ^ w - 1) ≤ targets) :
    (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
      (chainSetup P targets I)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← GXMSS.sampleStarts H h v
        let fillers ← sampleFillers I H
        let endpoints := GXMSS.endpoints P pp starts
        let registered := endpointTargets P pp starts
        pure ((⟨⟨starts, endpoints, fallback, registered, fallback⟩, fillers⟩ :
          ChainState PP T X H h v I), registered, [])) := by
  have hsetup := tcrChainSetup_run P targets pp hcap
  have hunif {Y : Type} (oa : ProbComp Y) (state : SM_DT_TCR_State T X) :
      (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf targets) pp)
        (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
    rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
      simulateQ_ofLift_eq_self]
    simp
  simp only [chainSetup, simulateQ_bind, StateT.run_bind]
  rw [hsetup]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  rw [hunif, bind_map_left]
  simp

private noncomputable def resultFromView
    (sk : GXMSS.SecretKey PP H h v)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v)) : Result PP H M R h v :=
  let (pk, forgery, history) := out
  ⟨pk, sk, forgery, history⟩

/-- Same-message/randomizer chain strategy for the actual interval interaction. Its original-hash
target capacity is the complete registered chain capacity; the fillers remain private and fixed. -/
noncomputable def sameMessageRandomizerChainTargetCollisionReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : SM_DT_TCR_Adversary (chainTCRProblem P) where
  State := ChainState PP T X H h v I
  choose := chainSetup P ((2 ^ h) * v * (2 ^ w)) I
  forge state pp := do
    let complete := state.complete
    let sk : GXMSS.Interval.SecretKey PP H h v I :=
      ⟨⟨pp, complete.starts, complete.endpoints⟩, state.fillers⟩
    let pk : GXMSS.PublicKey PP H :=
      ⟨GXMSS.IntervalMerkle.root P I pp complete.endpoints state.fillers, pp⟩
    let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
    pure (firstChainCandidate
      P enc complete pp (resultFromView sk.complete out))

private noncomputable def sameMessageRandomizerChainCollisionEvent
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v)) : Bool :=
  let (_, (epoch, message, signature), history) := out
  GXMSS.Interval.Unforgeability.activeMatchingEvent P enc K I sk out &&
    match history epoch with
    | some (first, some honest) =>
      decide ((first, honest.randomizer) = (message, signature.randomizer) ∧
        honest.ots ≠ signature.ots)
    | _ => false

/-- Native returned mass of active equal-message/randomizer forgeries whose OTS vectors differ.
Every successful signature is taken from the actual interval signing history. -/
noncomputable def sameMessageRandomizerChainCollisionExperiment
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (sameMessageRandomizerChainCollisionEvent P enc K I sk out)

private theorem viewFromKeys_support_pk [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v))
    (hout : out ∈ support (GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers)) :
    out.1 = (GXMSS.Interval.keys P I pp starts fillers).1 := by
  unfold ExperimentResult at out
  simp only [GXMSS.Interval.viewFromKeys, GXMSS.Interval.viewWithKeys] at hout
  dsimp only [ExperimentResult] at hout
  obtain ⟨pair, _, hret⟩ := support_bind_exists hout
  have heq := (mem_support_pure_iff _ _).mp hret
  subst out
  rfl

private theorem sameMessageRandomizerChainCandidate_wins_of_interval_collision
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v))
    (hout : out ∈ support (GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers))
    (hcollision : sameMessageRandomizerChainCollisionEvent P enc K I
      (GXMSS.Interval.keys P I pp starts fillers).2 out = true) :
    let registered := endpointTargets P pp starts
    let state : TCRKeyState PP T X H h v :=
      ⟨starts, GXMSS.endpoints P pp starts, fallback, registered, fallback⟩
    firstChainCandidateWins P pp registered
      (firstChainCandidate P enc state pp
        (resultFromView
          (⟨pp, starts, GXMSS.endpoints P pp starts⟩ : GXMSS.SecretKey PP H h v) out)) = true := by
  have hpk := viewFromKeys_support_pk P enc K I A pp starts fillers out hout
  rcases out with ⟨pk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hpk
  subst pk
  simp only [sameMessageRandomizerChainCollisionEvent, Bool.and_eq_true] at hcollision
  have hactive := hcollision.1
  cases hrecord : history epoch with
  | none => simp [hrecord] at hcollision
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp [hrecord] at hcollision
    | some honest =>
      have hp : (first, honest.randomizer) = (message, signature.randomizer) ∧
          honest.ots ≠ signature.ots := by
        simpa [hrecord] using hcollision.2
      obtain ⟨wr, hsig, hword⟩ := viewFromKeys_successful_record_signature P enc K I A pp
        starts fillers (_, (epoch, message, signature), history) hout
        epoch first honest hrecord
      have hhonestWord : enc.value pp first honest.randomizer epoch = some wr.1 := by
        rw [hsig]
        exact hword
      have hforgedWord : enc.value pp message signature.randomizer epoch = some wr.1 := by
        have hm : first = message := congrArg Prod.fst hp.1
        have hr : honest.randomizer = signature.randomizer := congrArg Prod.snd hp.1
        simpa only [← hm, ← hr] using hhonestWord
      have hopen : GXMSS.endpoints P pp starts epoch =
          fun i => P.chain pp epoch i (wr.1 i)
            (2 ^ w - 1 - (wr.1 i).val) (signature.ots i) := by
        simp only [GXMSS.Interval.Unforgeability.activeMatchingEvent, GXMSS.Interval.keys,
          GXMSS.keys, hforgedWord, Bool.and_eq_true] at hactive
        exact congrArg Prod.fst (of_decide_eq_true hactive.2).2
      have hhonestOTS : ∀ i, honest.ots i =
          P.chain pp epoch i 0 (wr.1 i) (starts epoch i) := by
        intro i
        simp [hsig, GXMSS.Interval.signatureOfWord, GXMSS.signatureOfWord,
          GXMSS.Interval.keys, GXMSS.keys]
      have hend : ∀ i, P.chain pp epoch i (wr.1 i)
          (2 ^ w - 1 - (wr.1 i).val) (honest.ots i) =
            P.chain pp epoch i (wr.1 i)
              (2 ^ w - 1 - (wr.1 i).val) (signature.ots i) := by
        intro i
        rw [hhonestOTS i, P.chain_complete_digit]
        exact congrFun hopen i
      obtain ⟨i, d, hi, hd,
        hvalid⟩ := firstChain_registeredTarget_wins P pp starts epoch
        wr.1 honest.ots signature.ots hhonestOTS hend hp.2
      simp only [firstChainCandidate, resultFromView, hrecord, hhonestWord,
        hforgedWord, ↓reduceIte]
      -- The direct scan's predicate contains the semireducible forged-tuple type.
      erw [hi]
      dsimp only
      erw [hd]
      exact hvalid

private noncomputable def sameMessageRandomizerChainCoupledProgram
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let registered := endpointTargets P pp starts
  let state : TCRKeyState PP T X H h v :=
    ⟨starts, GXMSS.endpoints P pp starts, fallback, registered, fallback⟩
  let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
  pure (firstChainCandidateWins P pp registered
    (firstChainCandidate P enc state pp
      (resultFromView (⟨pp, starts, GXMSS.endpoints P pp starts⟩ : GXMSS.SecretKey PP H h v) out)))

private theorem sameMessageRandomizerChainExperiment_eq_coupled
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment (sameMessageRandomizerChainTargetCollisionReduction P enc K I A) =
      sameMessageRandomizerChainCoupledProgram P enc K I A := by
  have hcap := chainProblem_capacity P
  unfold SM_DT_TCR_Experiment sameMessageRandomizerChainCoupledProgram
  simp only [sameMessageRandomizerChainTargetCollisionReduction]
  have hsetup (pp : PP) :
      (simulateQ (SM_DT_TCR_oracles (chainTCRProblem P) pp)
        (chainSetup P ((2 ^ h) * v * (2 ^ w)) I)).run ([], []) = (do
          let fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let fillers ← sampleFillers I H
          let endpoints := GXMSS.endpoints P pp starts
          let registered := endpointTargets P pp starts
          pure ((⟨⟨starts, endpoints, fallback, registered, fallback⟩, fillers⟩ :
            ChainState PP T X H h v I), registered, [])) := by
    change (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf ((2 ^ h) * v * (2 ^ w))) pp)
      (chainSetup P ((2 ^ h) * v * (2 ^ w)) I)).run ([], []) = _
    exact chainSetup_run P _ I pp (by
      simpa only [chainTCRProblem, SM_DT_TCR_Problem.standalone] using hcap)
  apply bind_congr
  intro pp
  rw [hsetup pp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro fillers
  apply bind_congr
  intro out
  dsimp only [GXMSS.Interval.keys, GXMSS.keys, firstChainCandidateWins,
    chainTCRProblem, SM_DT_TCR_Problem.standalone]
  split <;> simp_all only [ne_eq, Bool.decide_and, decide_not, PFunctor.FreeM.pure_inj]
  have decision {p q : Prop} [Decidable p] [Decidable q] :
      decide (¬p ∧ q) = (!decide p && decide q) := by
    simp only [Bool.decide_and, decide_not]
  exact decision

private noncomputable def sameMessageRandomizerChainCoupledCollisionProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
  pure (sameMessageRandomizerChainCollisionEvent
    P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out)

private theorem sameMessageRandomizerChainCoupledCollision_measure
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[sameMessageRandomizerChainCoupledCollisionProgram P enc K I A] =
      𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] := by
  unfold sameMessageRandomizerChainCoupledCollisionProgram
    sameMessageRandomizerChainCollisionExperiment GXMSS.Interval.keygen
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.Interval.viewFromKeys, bind_assoc, Function.comp_def] using
    (evalDist_bind_const ($ᵗ H : ProbComp H) (do
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
      pure (sameMessageRandomizerChainCollisionEvent
        P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out)))

/-- Active equal-pair OTS collisions are charged to the actual same-message/randomizer chain
adversary, retaining every native source outcome and the complete chain registration capacity. -/
theorem sameMessageRandomizerChainCollisionMass_le_advantage
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    ProbCompRuntime.probComp.evalDist (sameMessageRandomizerChainCollisionExperiment
      P enc K I A) {true} ≤
      SM_DT_TCR_Advantage (sameMessageRandomizerChainTargetCollisionReduction P enc K I A) := by
  rw [ProbCompRuntime.probComp_evalDist, ← sameMessageRandomizerChainCoupledCollision_measure]
  unfold SM_DT_TCR_Advantage
  rw [sameMessageRandomizerChainExperiment_eq_coupled]
  unfold sameMessageRandomizerChainCoupledCollisionProgram sameMessageRandomizerChainCoupledProgram
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fallback _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out hout
  by_cases hcollision : sameMessageRandomizerChainCollisionEvent P enc K I
      (GXMSS.Interval.keys P I pp starts fillers).2 out = true
  · have hwin := sameMessageRandomizerChainCandidate_wins_of_interval_collision P enc K I A pp
      starts fillers fallback out hout hcollision
    simp [hcollision, hwin]
  · have hfalse := Bool.eq_false_iff.mpr hcollision
    simp [hfalse]

/-- Chain-cut strategy in the original hash domain with the same pre-seed target registration and
fixed private fillers, using the actual interval view after seed reveal. -/
noncomputable def chainCutTargetCollisionReduction [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : SM_DT_TCR_Adversary (chainTCRProblem P) where
  State := ChainState PP T X H h v I
  choose := chainSetup P ((2 ^ h) * v * (2 ^ w)) I
  forge state pp := do
    let complete := state.complete
    let sk : GXMSS.Interval.SecretKey PP H h v I :=
      ⟨⟨pp, complete.starts, complete.endpoints⟩, state.fillers⟩
    let pk : GXMSS.PublicKey PP H :=
      ⟨GXMSS.IntervalMerkle.root P I pp complete.endpoints state.fillers, pp⟩
    let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
    pure (secondChainCandidate
      P enc complete pp (resultFromView sk.complete out))

private noncomputable def chainCutCollisionEvent
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v)) : Bool :=
  let (pk, (epoch, message, signature), history) := out
  GXMSS.Interval.Unforgeability.activeMatchingEvent P enc K I sk out &&
    match history epoch with
    | some (first, some honest) =>
      match enc.value pk.seed first honest.randomizer epoch,
          enc.value pk.seed message signature.randomizer epoch with
      | some honestWord, some forgedWord =>
        match (Fin.find? fun j => decide (forgedWord j < honestWord j)) with
        | none => false
        | some i => decide (P.chain pk.seed epoch i (forgedWord i)
            ((honestWord i).val - (forgedWord i).val) (signature.ots i) ≠ honest.ots i)
      | _, _ => false
    | _ => false

/-- Native active designated-cut collision experiment in the actual interval source view. -/
noncomputable def chainCutCollisionExperiment
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (chainCutCollisionEvent P enc K I sk out)

private theorem chainCutCandidate_wins_of_interval_collision
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) (fallback : H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v))
    (hout : out ∈ support (GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers))
    (hcollision : chainCutCollisionEvent P enc K I
      (GXMSS.Interval.keys P I pp starts fillers).2 out = true) :
    let registered := endpointTargets P pp starts
    let state : TCRKeyState PP T X H h v :=
      ⟨starts, GXMSS.endpoints P pp starts, fallback, registered, fallback⟩
    firstChainCandidateWins P pp registered
      (secondChainCandidate P enc state pp
        (resultFromView
          (⟨pp, starts, GXMSS.endpoints P pp starts⟩ : GXMSS.SecretKey PP H h v) out)) = true := by
  have hpk := viewFromKeys_support_pk P enc K I A pp starts fillers out hout
  rcases out with ⟨pk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hpk
  subst pk
  simp only [chainCutCollisionEvent, Bool.and_eq_true] at hcollision
  have hactive := hcollision.1
  cases hrecord : history epoch with
  | none => simp [hrecord] at hcollision
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp [hrecord] at hcollision
    | some honest =>
      obtain ⟨wr, hsig, hword⟩ := viewFromKeys_successful_record_signature P enc K I A pp
        starts fillers (_, (epoch, message, signature), history) hout
        epoch first honest hrecord
      have hhonestWord : enc.value pp first honest.randomizer epoch = some wr.1 := by
        rw [hsig]
        exact hword
      cases hforgedWord : enc.value pp message signature.randomizer epoch with
      | none =>
        simp [hrecord, GXMSS.Interval.keys, GXMSS.keys, hhonestWord,
          hforgedWord] at hcollision
      | some forgedWord =>
        cases hi : (Fin.find? fun j => decide (forgedWord j < wr.1 j)) with
        | none =>
          simp [hrecord, GXMSS.Interval.keys, GXMSS.keys, hhonestWord,
            hforgedWord, hi] at hcollision
        | some i =>
          have hneCut : P.chain pp epoch i (forgedWord i)
              ((wr.1 i).val - (forgedWord i).val) (signature.ots i) ≠ honest.ots i := by
            have hcut := hcollision.2
            simp only [hrecord, GXMSS.Interval.keys, GXMSS.keys, hhonestWord,
              hforgedWord, hi] at hcut
            exact of_decide_eq_true hcut
          have hopen : GXMSS.endpoints P pp starts epoch =
              fun i => P.chain pp epoch i (forgedWord i)
                (2 ^ w - 1 - (forgedWord i).val) (signature.ots i) := by
            simp only [GXMSS.Interval.Unforgeability.activeMatchingEvent, GXMSS.Interval.keys,
              GXMSS.keys, hforgedWord, Bool.and_eq_true] at hactive
            exact congrArg Prod.fst (of_decide_eq_true hactive.2).2
          have hhonestOTS : honest.ots i =
              P.chain pp epoch i 0 (wr.1 i) (starts epoch i) := by
            simp [hsig, GXMSS.Interval.signatureOfWord, GXMSS.signatureOfWord,
              GXMSS.Interval.keys, GXMSS.keys]
          have hend : P.chain pp epoch i (wr.1 i)
              (2 ^ w - 1 - (wr.1 i).val) (honest.ots i) =
                P.chain pp epoch i (forgedWord i)
                  (2 ^ w - 1 - (forgedWord i).val) (signature.ots i) := by
            rw [hhonestOTS, P.chain_complete_digit]
            exact congrFun hopen i
          obtain ⟨d, hd,
            hvalid⟩ := secondChain_registeredTarget_wins P pp starts epoch
            wr.1 forgedWord honest.ots signature.ots i hi hhonestOTS hend hneCut
          simpa [secondChainCandidate, resultFromView, hrecord, hhonestWord,
            hforgedWord,
            hi, hd] using hvalid

private noncomputable def chainCutCoupledProgram
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let registered := endpointTargets P pp starts
  let state : TCRKeyState PP T X H h v :=
    ⟨starts, GXMSS.endpoints P pp starts, fallback, registered, fallback⟩
  let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
  pure (firstChainCandidateWins P pp registered
    (secondChainCandidate P enc state pp
      (resultFromView (⟨pp, starts, GXMSS.endpoints P pp starts⟩ : GXMSS.SecretKey PP H h v) out)))

private theorem chainCutExperiment_eq_coupled
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment (chainCutTargetCollisionReduction P enc K I A) =
      chainCutCoupledProgram P enc K I A := by
  have hcap := chainProblem_capacity P
  unfold SM_DT_TCR_Experiment chainCutCoupledProgram
  simp only [chainCutTargetCollisionReduction]
  have hsetup (pp : PP) :
      (simulateQ (SM_DT_TCR_oracles (chainTCRProblem P) pp)
        (chainSetup P ((2 ^ h) * v * (2 ^ w)) I)).run ([], []) = (do
          let fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let fillers ← sampleFillers I H
          let endpoints := GXMSS.endpoints P pp starts
          let registered := endpointTargets P pp starts
          pure ((⟨⟨starts, endpoints, fallback, registered, fallback⟩, fillers⟩ :
            ChainState PP T X H h v I), registered, [])) := by
    change (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone P.thf ((2 ^ h) * v * (2 ^ w))) pp)
      (chainSetup P ((2 ^ h) * v * (2 ^ w)) I)).run ([], []) = _
    exact chainSetup_run P _ I pp (by
      simpa only [chainTCRProblem, SM_DT_TCR_Problem.standalone] using hcap)
  apply bind_congr
  intro pp
  rw [hsetup pp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro fillers
  apply bind_congr
  intro out
  dsimp only [GXMSS.Interval.keys, GXMSS.keys, firstChainCandidateWins,
    chainTCRProblem, SM_DT_TCR_Problem.standalone]
  split <;> simp_all only [ne_eq, Bool.decide_and, decide_not, PFunctor.FreeM.pure_inj]
  have decision {p q : Prop} [Decidable p] [Decidable q] :
      decide (¬p ∧ q) = (!decide p && decide q) := by
    simp only [Bool.decide_and, decide_not]
  exact decision

private noncomputable def chainCutCoupledCollisionProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let thf := P.thf
  let pp ← thf.seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← sampleFillers I H
  let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
  pure (chainCutCollisionEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out)

private theorem chainCutCoupledCollision_measure
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[chainCutCoupledCollisionProgram P enc K I A] =
      𝒟[chainCutCollisionExperiment P enc K I A] := by
  unfold chainCutCoupledCollisionProgram chainCutCollisionExperiment GXMSS.Interval.keygen
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.Interval.viewFromKeys, bind_assoc, Function.comp_def] using
    (evalDist_bind_const ($ᵗ H : ProbComp H) (do
      let starts ← GXMSS.sampleStarts H h v
      let fillers ← sampleFillers I H
      let out ← GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers
      pure (chainCutCollisionEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out)))

/-- Active designated-cut collisions are charged to the actual chain-cut
adversary, retaining every native source outcome and the complete chain registration capacity. -/
theorem chainCutCollisionMass_le_advantage
      [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    ProbCompRuntime.probComp.evalDist (chainCutCollisionExperiment P enc K I A) {true} ≤
      SM_DT_TCR_Advantage (chainCutTargetCollisionReduction P enc K I A) := by
  rw [ProbCompRuntime.probComp_evalDist, ← chainCutCoupledCollision_measure]
  unfold SM_DT_TCR_Advantage
  rw [chainCutExperiment_eq_coupled]
  unfold chainCutCoupledCollisionProgram chainCutCoupledProgram
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fallback _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro fillers _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out hout
  by_cases hcollision : chainCutCollisionEvent P enc K I
      (GXMSS.Interval.keys P I pp starts fillers).2 out = true
  · have hwin := chainCutCandidate_wins_of_interval_collision P enc K I A pp
      starts fillers fallback out hout hcollision
    simp [hcollision, hwin]
  · have hfalse := Bool.eq_false_iff.mpr hcollision
    simp [hfalse]

end GXMSS.Interval.Reductions.Chain

namespace GXMSS.Interval.Unforgeability
open IncomparableEncoding ENNReal OracleComp OracleSpec TweakableHash
  GXMSS.Reductions GXMSS.Interval.Reductions GXMSS.Interval.Reductions.Chain
  GXMSS.IntervalMerkle SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- The actual active remainder removes encoding and equal-payload OTS collisions, then keeps
its designated chain cut. The complete signing history and returned failures remain observable. -/
noncomputable def activeRemainderExperiment
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let (pk, sk) ← GXMSS.Interval.keygen P I
  let view ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
  pure (let (publicKey, forgery, history) := view
    let (epoch, message, signature) := forgery
    let complete := sk.complete
    let observedKey : GXMSS.Interval.SecretKey PP H h v I :=
      ⟨⟨publicKey.seed, complete.endpoints, complete.endpoints⟩, sk.fillers⟩
    let collision := if Epoch.IsActive I epoch then
      match history epoch with
      | some (first, some honest) =>
        match enc.value publicKey.seed first honest.randomizer epoch,
            enc.value publicKey.seed message signature.randomizer epoch with
        | some honestWord, some forgedWord => decide (honestWord = forgedWord ∧
            (first, honest.randomizer) ≠ (message, signature.randomizer))
        | _, _ => false
      | _ => false
      else false
    activeMatchingEvent P enc K I observedKey view && !collision &&
      (match history epoch with
      | some (first, some honest) => decide ((first, honest.randomizer) ≠
          (message, signature.randomizer) ∨ honest.ots = signature.ots)
      | _ => true) &&
      designatedCutHolds P enc ⟨publicKey, complete, forgery, history⟩)

private noncomputable def intervalResultFromView {I : Interval h}
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v)) : Result PP H M R h v :=
  let complete := sk.complete
  resultFromView complete out

private theorem activeMatching_partition_at_keys
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v)
    (pp : PP) (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v))
    (hout : out ∈ support (GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers))
    (hactive : activeMatchingEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2
      out = true) :
    intervalEncodingCollision enc I out = true ∨
      sameMessageRandomizerChainCollisionEvent
        P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out = true ∨
      chainCutCollisionEvent P enc K I (GXMSS.Interval.keys P I pp starts fillers).2 out = true ∨
      intervalChainRemainderObservation P enc K I fillers
        (intervalResultFromView (GXMSS.Interval.keys P I pp starts fillers).2 out) = true := by
  have hpk := viewFromKeys_support_pk P enc K I A pp starts fillers out hout
  rcases out with ⟨pk, ⟨epoch, message, signature⟩, history⟩
  dsimp only at hpk
  subst pk
  by_cases hec : intervalEncodingCollision enc I
      ((GXMSS.Interval.keys P I pp starts fillers).1, (epoch, message, signature), history) = true
  · exact Or.inl hec
  by_cases hfirst : sameMessageRandomizerChainCollisionEvent P enc K I
      (GXMSS.Interval.keys P I pp starts fillers).2
      ((GXMSS.Interval.keys P I pp starts fillers).1, (epoch, message, signature), history) = true
  · exact Or.inr (Or.inl hfirst)
  have hremGate : (match history epoch with
      | some (first, some honest) => decide ((first, honest.randomizer) ≠
          (message, signature.randomizer) ∨ honest.ots = signature.ots)
      | _ => true) = true := by
    cases hs : history epoch with
    | none => rfl
    | some entry =>
      rcases entry with ⟨first, answer⟩
      cases answer with
      | none => rfl
      | some honest =>
        simpa only [sameMessageRandomizerChainCollisionEvent, hactive, hs, Bool.true_and,
          decide_eq_true_eq, not_and_or, not_not] using hfirst
  let result := intervalResultFromView (GXMSS.Interval.keys P I pp starts fillers).2
    ((GXMSS.Interval.keys P I pp starts fillers).1, (epoch, message, signature), history)
  by_cases hcut : designatedCutHolds P enc result = true
  · exact Or.inr (Or.inr (Or.inr (by
      simp only [intervalChainRemainderObservation, intervalResultFromView, resultFromView,
        Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨⟨?_, Bool.eq_false_iff.mpr hec⟩, hremGate⟩, hcut⟩
      exact hactive)))
  · right; right; left
    cases hs : history epoch with
    | none =>
      simp [result, intervalResultFromView, resultFromView, designatedCutHolds,
        forgedEpochSource, hs] at hcut
    | some entry =>
      rcases entry with ⟨first, answer⟩
      cases answer with
      | none =>
        simp [result, intervalResultFromView, resultFromView, designatedCutHolds,
          forgedEpochSource, hs] at hcut
      | some honest =>
        obtain ⟨wr, hsig, hh⟩ := viewFromKeys_successful_record_signature P enc K I A pp
          starts fillers (_, (epoch, message, signature), history) hout epoch first honest hs
        have hhonest : enc.value pp first honest.randomizer epoch = some wr.1 := by
          rw [hsig]
          exact hh
        cases hf : enc.value pp message signature.randomizer epoch with
        | none => simp [activeMatchingEvent, GXMSS.Interval.keys, GXMSS.keys, hf] at hactive
        | some forgedWord =>
          have he : Epoch.IsActive I epoch := by
            simp only [activeMatchingEvent, GXMSS.Interval.keys, GXMSS.keys, hf,
              Bool.and_eq_true] at hactive
            exact (of_decide_eq_true hactive.2).1
          -- Equal words force the exact recorded message/signature pair, contradicting freshness.
          have hne : wr.1 ≠ forgedWord := by
            intro heq
            have hpair : (first, honest.randomizer) = (message, signature.randomizer) := by
              have hc := hec
              simp only [intervalEncodingCollision, he, ite_true, hs,
                GXMSS.Interval.keys, GXMSS.keys, hhonest, hf, heq, true_and,
                decide_eq_true_eq, not_not] at hc
              exact hc
            have hots : honest.ots = signature.ots := by
              simpa only [hs, hpair, ne_eq, not_true_eq_false, false_or,
                decide_eq_true_eq] using hremGate
            have hpath : honest.path = signature.path := by
              have ha := hactive
              simp only [activeMatchingEvent, GXMSS.Interval.keys, GXMSS.keys, hf,
                Bool.and_eq_true] at ha
              have hp := congrArg Prod.snd (of_decide_eq_true ha.2).2
              rw [hsig]
              exact hp
            have hsignature : honest = signature := by
              cases honest with
              | mk r ots path =>
                cases signature with
                | mk r' ots' path' =>
                  dsimp only at hpair hots hpath
                  have hr := congrArg Prod.snd hpair
                  cases hr; cases hots; cases hpath
                  rfl
            have hmsg := congrArg Prod.fst hpair
            have ha := hactive
            simp only [activeMatchingEvent, Bool.and_eq_true] at ha
            have hfresh := ha.1
            simp only [strongValid, Bool.and_eq_true] at hfresh
            change first = message at hmsg
            have hnot : first ≠ message := by
              intro hmessage
              have hf := hfresh.2
              simp only [strongFresh, hs, hsignature, decide_eq_true_eq] at hf
              exact hf (by rw [hmessage])
            exact hnot hmsg
          obtain ⟨coordinate, hcoordinate⟩ := (enc.incomparableWords_of_successes
            pp pp first message honest.randomizer signature.randomizer epoch epoch
            hhonest hf hne).2
          obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
            (Fin.isSome_find?_of_eq_true
              (p := fun j => decide (forgedWord j < wr.1 j))
              (i := coordinate) (decide_eq_true hcoordinate))
          have hneq : P.chain pp epoch i (forgedWord i)
              ((wr.1 i).val - (forgedWord i).val) (signature.ots i) ≠ honest.ots i := by
            simp only [result, intervalResultFromView, resultFromView, designatedCutHolds,
              forgedEpochSource, hs, GXMSS.Interval.keys, GXMSS.keys, hhonest, hf, hi] at hcut
            intro heq
            exact hcut (decide_eq_true heq)
          unfold chainCutCollisionEvent
          dsimp only
          rw [hactive]
          simp only [hs, GXMSS.Interval.keys, GXMSS.keys, hhonest, hf, hi, Bool.true_and]
          exact decide_eq_true hneq

private theorem bind_true_mass_le_four {α : Type} (draw : ProbComp α)
    (s a b c d : α → ProbComp Bool)
    (hle : ∀ x ∈ support draw, 𝒟[s x] {true} ≤
      𝒟[a x] {true} + 𝒟[b x] {true} + 𝒟[c x] {true} + 𝒟[d x] {true}) :
    𝒟[draw >>= s] {true} ≤ 𝒟[draw >>= a] {true} + 𝒟[draw >>= b] {true} +
      𝒟[draw >>= c] {true} + 𝒟[draw >>= d] {true} := by
  let : MeasurableSpace α := ⊤
  simp only [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  simp only [← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
    Measurable fun x : α => 𝒟[a x] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun x : α => 𝒟[a x] {true} + 𝒟[b x] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun x : α => 𝒟[a x] {true} + 𝒟[b x] {true} + 𝒟[c x] {true})]
  exact MeasureTheory.lintegral_mono_ae
    (evalDist.ae_of_forall_mem_support draw _ MeasurableSet.of_discrete hle)

private theorem bool_mass_le_four (s a b c d : Bool)
    (h : s = true → a = true ∨ b = true ∨ c = true ∨ d = true) :
    𝒟[(pure s : ProbComp Bool)] {true} ≤
      𝒟[(pure a : ProbComp Bool)] {true} + 𝒟[(pure b : ProbComp Bool)] {true} +
        𝒟[(pure c : ProbComp Bool)] {true} + 𝒟[(pure d : ProbComp Bool)] {true} := by
  cases s <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Native active matching mass is covered by the actual encoding and two chain-collision
experiments and the active remainder. Encoding collisions are restricted by active matching
in the pointwise partition, then enlarged to the original encoding experiment by monotonicity. -/
theorem activeMatchingMass_le_collision_masses_add_remainder
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) :
    𝒟[activeMatchingExperiment P enc K I A] {true} ≤
      𝒟[encodingCollisionExperiment P enc K I A] {true} +
        𝒟[sameMessageRandomizerChainCollisionExperiment P enc K I A] {true} +
        𝒟[chainCutCollisionExperiment P enc K I A] {true} +
        𝒟[activeRemainderExperiment P enc K I A] {true} := by
  have hm := bind_true_mass_le_four (retainedSource P enc K I A)
    (fun z => pure (activeMatchingEvent P enc K I z.1 z.2))
    (fun z => pure (intervalEncodingCollision enc I z.2))
    (fun z => pure (sameMessageRandomizerChainCollisionEvent P enc K I z.1 z.2))
    (fun z => pure (chainCutCollisionEvent P enc K I z.1 z.2))
    (fun z => let (sk, view) := z
      pure (intervalChainRemainderObservation P enc K I sk.fillers
        (resultFromView sk.complete view))) ?_
  · have hremEq : (retainedSource P enc K I A >>= fun z =>
        let (sk, view) := z
        pure (intervalChainRemainderObservation P enc K I sk.fillers
          (resultFromView sk.complete view))) = activeRemainderExperiment P enc K I A := by
      unfold retainedSource activeRemainderExperiment
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      rintro ⟨pk, sk⟩
      apply bind_congr
      rintro ⟨publicKey, ⟨epoch, message, signature⟩, history⟩
      rfl
    rw [hremEq] at hm
    simpa [activeMatchingExperiment, encodingCollisionExperiment,
      sameMessageRandomizerChainCollisionExperiment,
      chainCutCollisionExperiment, retainedSource, monad_norm] using hm
  · rintro ⟨sk, out⟩ hz
    simp only [retainedSource, GXMSS.Interval.keygen, bind_assoc, pure_bind] at hz
    obtain ⟨pp, _, hz⟩ := support_bind_exists hz
    obtain ⟨starts, _, hz⟩ := support_bind_exists hz
    obtain ⟨fillers, _, hz⟩ := support_bind_exists hz
    obtain ⟨view, hview, hret⟩ := support_bind_exists hz
    have heq := (mem_support_pure_iff _ _).mp hret
    cases heq
    apply bool_mass_le_four
    intro ha
    exact activeMatching_partition_at_keys P enc K I A pp starts fillers out hview ha

end GXMSS.Interval.Unforgeability

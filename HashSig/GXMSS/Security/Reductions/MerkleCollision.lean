/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.CompleteBounds
import all HashSig.GXMSS.Security.Auxiliary.CompleteBounds
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.Auxiliary.SourcePartition
import all HashSig.GXMSS.Security.Auxiliary.SourcePartition
public import HashSig.GXMSS.Security.Reductions.Experiments
import all HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.MerkleForgery
import all HashSig.GXMSS.Security.Reductions.MerkleForgery
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Merkle collision reduction bound

The actual Merkle target-collision experiment is coupled to the source interaction and
bounds the native mass of inconsistent openings.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

private def merkleCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : GXMSS.Reductions.TCRKeyState PP T X H h v) (pp : PP)
    (out : GXMSS.Reductions.Result PP H M R h v) : ℕ × X :=
  let forgery := out.forgery
  let epoch := forgery.1
  let messageAndSignature := forgery.2
  let signature := messageAndSignature.2
  match GXMSS.Reductions.forgedLeaf? hash enc out with
  | none => (0, hash.vectorInput (state.endpoints 0))
  | some forgedLeaf =>
    match hash.findMerkleCollision pp epoch (state.endpoints epoch)
      forgedLeaf (hash.authPath pp state.endpoints epoch) signature.path with
    | none => (0, hash.vectorInput (state.endpoints 0))
    | some collision =>
      (GXMSS.Reductions.registeredIndex state.targets collision.tweak collision.first,
        collision.second)

private def merkleCandidateWins [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (history : List (T × X)) (candidate : ℕ × X) : Bool :=
  match history[candidate.1]? with
  | none => false
  | some (t, first) =>
    decide (candidate.2 ≠ first ∧
      (HashInstance.thf hash).eval pp t candidate.2 =
        (HashInstance.thf hash).eval pp t first)

private theorem tcrDecision_eq [DecidableEq X] (x y : X) (q : Prop) [Decidable q] :
    decide (x ≠ y ∧ q) = (!decide (x = y) && decide q) := by
  simp only [Bool.decide_and, decide_not]

/-- Every returned source result with an unequal complete opening makes the actual Merkle
reduction candidate win against the exact honest registration history. -/
private theorem merkleCandidateWins_of_difference
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H) (fallback : H)
    (forgery : SyncSignatureUnforgeability.Forgery (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (hdiff : GXMSS.Reductions.merkleDifferenceObservation hash enc K
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩ = true) :
    let endpoints := GXMSS.endpoints hash pp starts
    let registered := GXMSS.Reductions.endpointTargets hash pp starts ++
      GXMSS.Reductions.merkleTargets hash pp endpoints
    let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
      ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
    let out : GXMSS.Reductions.Result PP H M R h v :=
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩
    merkleCandidateWins hash pp registered (merkleCandidate hash enc state pp out) = true := by
  let endpoints := GXMSS.endpoints hash pp starts
  let registered := GXMSS.Reductions.endpointTargets hash pp starts ++
    GXMSS.Reductions.merkleTargets hash pp endpoints
  let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
    ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
  let out : GXMSS.Reductions.Result PP H M R h v :=
    ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
      forgery, history⟩
  let epoch := forgery.1
  let messageAndSignature := forgery.2
  let message := messageAndSignature.1
  let signature := messageAndSignature.2
  have hleaf : ∃ leaf, GXMSS.Reductions.forgedLeaf? hash enc out = some leaf := by
    cases h : GXMSS.Reductions.forgedLeaf? hash enc out with
    | none => simp [GXMSS.Reductions.merkleDifferenceObservation, out, h] at hdiff
    | some leaf => exact ⟨leaf, rfl⟩
  obtain ⟨leaf, hleaf⟩ := hleaf
  have hsplit := hdiff
  simp only [GXMSS.Reductions.merkleDifferenceObservation,
    Bool.and_eq_true] at hsplit
  have hne : (endpoints epoch, hash.authPath pp endpoints epoch) ≠
      (leaf, signature.path) := by
    let publicKey := out.pk
    let secretKey := out.sk
    have hne' := hsplit.2
    change (match GXMSS.Reductions.forgedLeaf? hash enc out with
      | none => false
      | some leaf => decide ((secretKey.endpoints epoch,
          hash.authPath publicKey.seed secretKey.endpoints epoch) ≠
        (leaf, signature.path))) = true at hne'
    rw [hleaf] at hne'
    simpa only [publicKey, secretKey, out, GXMSS.keys, endpoints] using
      (of_decide_eq_true hne')
  have hstrong : GXMSS.Reductions.sourceStrongObservation hash enc K out = true := by
    exact hsplit.1
  have hverify : GXMSS.verify hash enc (GXMSS.keys hash pp starts).1
      epoch message signature = true := by
    have hstrong' := hstrong
    simp only [GXMSS.Reductions.sourceStrongObservation,
      GXMSS.Reductions.sourceObservation,
      SyncSignatureUnforgeability.strongValid, GXMSS.scheme,
      Bool.and_eq_true] at hstrong'
    exact hstrong'.1
  obtain ⟨word, hword, hleafValue⟩ := Option.map_eq_some_iff.mp hleaf
  have hword' : enc.value pp message signature.randomizer epoch =
      some word := by
    simpa only [out, GXMSS.Reductions.forgedLeaf?, GXMSS.keys] using hword
  have hleafValue' : (fun i => hash.chain pp epoch i (word i)
      (2 ^ w - 1 - (word i).val) (signature.ots i)) = leaf := by
    simpa only [out, GXMSS.Reductions.forgedLeaf?, GXMSS.keys] using hleafValue
  have hroot : hash.recoverRoot pp epoch leaf signature.path =
      hash.merkleRoot pp endpoints := by
    have hverify' : hash.recoverRoot pp epoch
        (fun i => hash.chain pp epoch i (word i)
          (2 ^ w - 1 - (word i).val) (signature.ots i)) signature.path =
        hash.merkleRoot pp (GXMSS.endpoints hash pp starts) := by
      simp only [GXMSS.verify, GXMSS.keys, hword'] at hverify
      exact of_decide_eq_true hverify
    rw [hleafValue'] at hverify'
    simpa only [endpoints] using hverify'
  obtain ⟨collision, hcollision, _, hlookup, _, hwin⟩ :=
    merkleCollision_registeredTarget_wins hash hv pp starts epoch leaf
      signature.path hne hroot
  dsimp only [epoch, signature, messageAndSignature] at hcollision
  simpa only [merkleCandidateWins, merkleCandidate, state, out, registered,
    hleaf, hcollision, hlookup] using hwin

private def merkleCoupledProgram [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let endpoints := GXMSS.endpoints hash pp starts
  let registered := GXMSS.Reductions.endpointTargets hash pp starts ++
    GXMSS.Reductions.merkleTargets hash pp endpoints
  let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
    ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← GXMSS.Reductions.runWithKeys hash enc K adv pk sk
  pure (merkleCandidateWins hash pp registered (merkleCandidate hash enc state pp out))

private def merkleCoupledDifferenceProgram [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← GXMSS.Reductions.runWithKeys hash enc K adv pk sk
  pure (GXMSS.Reductions.merkleDifferenceObservation hash enc K out)

/-- The extra private fallback draw is lossless and invisible to the source difference
observation, so it preserves the full native Boolean measure. -/
private theorem merkleCoupledDifference_evalDist_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    𝒟[merkleCoupledDifferenceProgram hash enc K adv] =
      𝒟[GXMSS.Reductions.merkleDifferenceObservation hash enc K <$>
        GXMSS.Reductions.sourceProgram hash enc K adv] := by
  unfold merkleCoupledDifferenceProgram GXMSS.Reductions.sourceProgram GXMSS.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.keys, bind_assoc, Function.comp_def] using
    (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H)
      (do
        let starts ← GXMSS.sampleStarts H h v
        let (pk, sk) := GXMSS.keys hash pp starts
        let out ← GXMSS.Reductions.runWithKeys hash enc K adv pk sk
        pure (GXMSS.Reductions.merkleDifferenceObservation hash enc K out)))

/-- The authoritative Merkle TCR experiment is the faithful coupled execution, including its
private fallback draw and exact ordered challenge history. -/
private theorem merkleExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) =
        merkleCoupledProgram hash enc K adv := by
  have hcap := GXMSS.Reductions.merkleProblem_capacity hash hv
  unfold SM_DT_TCR_Experiment merkleCoupledProgram
  simp only [GXMSS.Reductions.merkleTargetCollisionReduction]
  have hsetup (pp : PP) :
      (simulateQ (SM_DT_TCR_oracles (GXMSS.Reductions.merkleTCRProblem hash) pp)
        (GXMSS.Reductions.tcrKeySetup hash
          (2 * (2 ^ h) * v * (2 ^ w)))).run ([], []) = (do
          let fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let endpoints := GXMSS.endpoints hash pp starts
          let registered := GXMSS.Reductions.endpointTargets hash pp starts ++
            GXMSS.Reductions.merkleTargets hash pp endpoints
          pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered,
              fallback⟩ : GXMSS.Reductions.TCRKeyState PP T X H h v),
            registered, ([] : List T))) := by
    change (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf
        (2 * (2 ^ h) * v * (2 ^ w))) pp)
      (GXMSS.Reductions.tcrKeySetup hash
        (2 * (2 ^ h) * v * (2 ^ w)))).run ([], []) = _
    exact GXMSS.Reductions.tcrKeySetup_run hash _ pp (by
      simpa only [GXMSS.Reductions.merkleTCRProblem,
        SM_DT_TCR_Problem.standalone] using hcap)
  apply bind_congr
  intro pp
  rw [hsetup pp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro out
  let forgery := out.forgery
  let epoch := forgery.1
  let messageAndSignature := forgery.2
  let signature := messageAndSignature.2
  cases hleaf : GXMSS.Reductions.forgedLeaf? hash enc out with
  | none =>
    simp only [merkleCandidate, merkleCandidateWins, hleaf,
      GXMSS.Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
      pure_bind, List.length_append, GXMSS.Reductions.endpointTargets_length,
      GXMSS.Reductions.merkleTargets_length, add_pos_iff,
      CanonicallyOrderedAdd.mul_pos, Order.lt_two_iff, zero_le, pow_pos,
      true_and, tsub_pos_iff_lt, Nat.one_lt_two_pow_iff,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      Nat.one_lt_pow_iff, Std.le_refl, or_true, getElem?_pos,
      PFunctor.FreeM.pure_inj]
    exact tcrDecision_eq _ _ _
  | some leaf =>
    cases hcollision : hash.findMerkleCollision pp epoch
        (GXMSS.endpoints hash pp starts epoch) leaf
        (hash.authPath pp (GXMSS.endpoints hash pp starts) epoch)
        signature.path with
    | none =>
      dsimp only [epoch, signature, messageAndSignature, forgery] at hcollision
      simp only [merkleCandidate, merkleCandidateWins, hleaf, hcollision,
        GXMSS.Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
        pure_bind, List.length_append, GXMSS.Reductions.endpointTargets_length,
        GXMSS.Reductions.merkleTargets_length, add_pos_iff,
        CanonicallyOrderedAdd.mul_pos, Order.lt_two_iff, zero_le, pow_pos,
        true_and, tsub_pos_iff_lt, Nat.one_lt_two_pow_iff,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        Nat.one_lt_pow_iff, Std.le_refl, or_true, getElem?_pos,
        PFunctor.FreeM.pure_inj]
      exact tcrDecision_eq _ _ _
    | some collision =>
      dsimp only [epoch, signature, messageAndSignature, forgery] at hcollision
      simp only [merkleCandidate, merkleCandidateWins, hleaf, hcollision,
        GXMSS.Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
        pure_bind]
      cases hlookup : (GXMSS.Reductions.endpointTargets hash pp starts ++
          GXMSS.Reductions.merkleTargets hash pp
            (GXMSS.endpoints hash pp starts))[
          GXMSS.Reductions.registeredIndex
            (GXMSS.Reductions.endpointTargets hash pp starts ++
              GXMSS.Reductions.merkleTargets hash pp
                (GXMSS.endpoints hash pp starts))
            collision.tweak collision.first]? with
      | none => rfl
      | some target =>
        cases target with
        | mk t first =>
          by_cases heq : collision.second = first <;>
            simp [SM_DT_TCR_Problem.standalone, heq]

/-- Every returned source result retains the fixed keys supplied to the interaction. -/
private theorem runWithKeys_support_keys
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (out : GXMSS.Reductions.Result PP H M R h v)
    (hout : out ∈ support
      (GXMSS.Reductions.runWithKeys hash enc K adv pk sk)) :
    out.pk = pk ∧ out.sk = sk := by
  simp only [GXMSS.Reductions.runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure] at hret
  subst out
  exact ⟨rfl, rfl⟩

/-- The faithful coupling maps each returned unequal-opening source win to a returned
authoritative target-collision win; abort and unreturned mass remain in both computations. -/
private theorem merkleCoupledDifference_le_win
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    𝒟[merkleCoupledDifferenceProgram hash enc K adv] {true} ≤
      𝒟[merkleCoupledProgram hash enc K adv] {true} := by
  unfold merkleCoupledDifferenceProgram merkleCoupledProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (HashInstance.thf hash).seedGen _ _ (by measurability)
  intro pp _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    ($ᵗ H : ProbComp H) _ _ (by measurability)
  intro fallback _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (GXMSS.sampleStarts H h v) _ _ (by measurability)
  intro starts _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (GXMSS.Reductions.runWithKeys hash enc K adv
      (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2)
    _ _ (by measurability)
  intro out hout
  obtain ⟨hpk, hsk⟩ := runWithKeys_support_keys hash enc K adv
    (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hout
  cases out with
  | mk pk sk forgery history =>
    dsimp at hpk hsk
    subst pk
    subst sk
    by_cases hdiff : GXMSS.Reductions.merkleDifferenceObservation hash enc K
        ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
          forgery, history⟩ = true
    · have hwin := merkleCandidateWins_of_difference hash enc K hv pp starts
        fallback forgery history hdiff
      simp [hdiff, hwin]
    · have hfalse : GXMSS.Reductions.merkleDifferenceObservation hash enc K
          ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
            forgery, history⟩ = false := Bool.eq_false_iff.mpr hdiff
      simp [hfalse]

/-- The exact first Merkle target-collision hop for the adopted strong synchronized-signature
experiment and the executable stand-alone SM-DT-TCR reduction. -/
theorem first_merkle_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    FirstMerkleTargetCollisionBound hash enc K hv adv := by
  unfold FirstMerkleTargetCollisionBound
  change SyncSignatureUnforgeability.strongUnforgeableExp (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp adv {true} ≤
    SM_DT_TCR_Advantage
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) +
      GXMSS.Reductions.gameOneAdvantage hash enc K adv
  rw [← GXMSS.Reductions.sourceStrongOutputMeasure_eq_strongUnforgeableExp]
  have hdiff : ProbCompRuntime.probComp.evalDist
        (GXMSS.Reductions.merkleDifferenceObservation hash enc K <$>
          GXMSS.Reductions.sourceProgram hash enc K adv) {true} ≤
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) := by
    rw [ProbCompRuntime.probComp_evalDist,
      ← merkleCoupledDifference_evalDist_eq_source]
    change 𝒟[merkleCoupledDifferenceProgram hash enc K adv] {true} ≤
      𝒟[SM_DT_TCR_Experiment
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv)] {true}
    rw [merkleExperiment_eq_coupled]
    exact merkleCoupledDifference_le_win hash enc K hv adv
  calc
    _ ≤ GXMSS.Reductions.gameOneAdvantage hash enc K adv +
        ProbCompRuntime.probComp.evalDist
          (GXMSS.Reductions.merkleDifferenceObservation hash enc K <$>
            GXMSS.Reductions.sourceProgram hash enc K adv) {true} :=
      sourceStrongWinningMass_le_gameOne_add_merkleDifference hash enc K adv
    _ ≤ GXMSS.Reductions.gameOneAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) :=
      add_le_add_right hdiff _
    _ = _ := add_comm _ _


end

end GXMSS.Unforgeability

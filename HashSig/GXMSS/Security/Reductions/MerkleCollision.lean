/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Reductions.JointReductions
import all HashSig.GXMSS.Security.Reductions.JointReductions
public import HashSig.GXMSS.Security.Auxiliary.TCRSimulation
public import VCVio.CryptoFoundations.SyncSignatureAlg.Security
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD

import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.GuessingGames
import all HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.SplicedChain
import all HashSig.GXMSS.Security.Reductions.ChainHybrid

/-!
# Merkle target collision bound

The source strong-winning measure is separated into Game 1 and a Merkle difference event.
A coupled source and target-collision experiment bounds the latter event.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Every execution path of the source adversary has at most `qs` signing calls.  Repeated
calls and calls answered with failure count; ambient uniform calls do not. -/
@[expose]
def SigningQueryBound (qs : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) : Prop :=
  ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs

/-- The concrete separate-term reduction inequality underlying Theorem 1. The parameter `qs`
controls the encoding target-collision transcript, and `K` controls its retry law. The source
adversary has the explicit pathwise signing-query bound; the authoritative adversary types preserve
their own sampling, seed-reveal and oracle disciplines. This proposition does not claim
reduction-query or running-time bounds. -/
@[expose]
def StrongUnforgeabilityReductionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (advGXMSS : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (advMerkleTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))))
    (advEncodingTCR : Encoding.TargetCollisionResistance.Adversary
  (Encoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K))
    (advFirstChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advSecondChainTCR : SM_DT_TCR_Adversary
      (SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))))
    (advUD : SM_DT_UD_Adversary
  (SM_DT_UD_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective
        ($ᵗ H) ($ᵗ H) 1))
    (advPRE : SM_DT_PRE_Adversary
  (SM_DT_PRE_Problem.standalone (HashInstance.thf hash) (HashInstance.digestInput hash)
    (HashInstance.digestInput hash).injective 1)) :
    Prop :=
  SigningQueryBound qs advGXMSS →
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    SM_DT_TCR_Advantage advMerkleTCR +
      Encoding.TargetCollisionResistance.advantage advEncodingTCR +
      SM_DT_TCR_Advantage advFirstChainTCR + SM_DT_TCR_Advantage advSecondChainTCR +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) * SM_DT_UD_Advantage advUD +
          SM_DT_PRE_Advantage advPRE)

/-- Separate correctness obligation from Lemma 3. The pointwise one-attempt failure is `q`, exact
independent retry failure is `q ^ K`, and `δ ^ K` is only the uniform upper bound and resulting
correctness loss. None of these quantities is added to the security inequality above. -/
@[expose]
def CorrectnessFailureBound [SampleableType H] [SampleableType R]
    [Fintype R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (q : PP → M → Fin (2 ^ h) → ℝ≥0∞) (δ : ℝ≥0∞) : Prop :=
  enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ ∧
    (∀ pp msg ep, q pp msg ep = enc.failureMass ProbCompRuntime.probComp ($ᵗ R) pp msg ep) ∧
    (∀ pp msg ep, IncomparableEncoding.Retry.failureMass enc ProbCompRuntime.probComp
      ($ᵗ R) pp msg ep K = (q pp msg ep) ^ K) ∧
    (∀ pp msg ep, (q pp msg ep) ^ K ≤ δ ^ K) ∧
    (GXMSS.scheme hash enc K).Complete ProbCompRuntime.probComp (δ ^ K)

/-- The exact Game 0-to-Game 1 Merkle target-collision inequality.  The left side is the adopted
post-runtime strong-unforgeability winning mass, `gameOneAdvantage` observes the actual Game 1
program after the same partial runtime evaluation, and the other summand is the authoritative
SM-DT-TCR experiment for the executable reduction.  This proposition introduces no conditioning
or support-only surrogate. -/
@[expose]
def FirstMerkleTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v)
    (advGXMSS : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) : Prop :=
  SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp advGXMSS ≤
    SM_DT_TCR_Advantage
        (Reductions.merkleTargetCollisionReduction hash enc K hv advGXMSS) +
      Reductions.gameOneAdvantage hash enc K advGXMSS

/-- The source winning mass is bounded by the two disjoint observations on the same partial
interaction. This statement preserves the runtime's unreturned mass. -/
theorem sourceStrongWinningMass_le_gameOne_add_merkleDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    Reductions.sourceStrongOutputMeasure hash enc K adv {true} ≤
      Reductions.gameOneAdvantage hash enc K adv +
        ProbCompRuntime.probComp.evalDist
          (Reductions.merkleDifferenceObservation hash enc K <$>
            Reductions.sourceProgram hash enc K adv) {true} := by
  simp only [Reductions.sourceStrongOutputMeasure,
    Reductions.gameOneAdvantage, Reductions.gameOneOutputMeasure,
    Reductions.gameOne, ProbCompRuntime.probComp_evalDist]
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (Reductions.sourceProgram hash enc K adv)
    (fun out => pure (Reductions.sourceStrongObservation hash enc K out))
    (fun out => pure (Reductions.gameOneObservation hash enc K out))
    (fun out => pure (Reductions.merkleDifferenceObservation hash enc K out))
    (by measurability)
  intro out _
  rw [Reductions.sourceStrongObservation_eq_gameOne_or_merkleDifference]
  cases Reductions.gameOneObservation hash enc K out <;>
    cases Reductions.merkleDifferenceObservation hash enc K out <;>
    simp

/-- The exact universally closed Merkle-forgery proposition audited below. -/
@[expose]
def ValidForgeryYieldsMerkleCollisionStatement [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h))
    (forgedMessage : M) (forgedRandomizer : R) (forgedWord : Codeword v (2 ^ w))
    (forgedOTS : Fin v → H) (forgedPath : Fin h → H) : Prop :=
  let honestEndpoints := sk.endpoints
  let honestLeaf := honestEndpoints epoch
  let honestPath := hash.authPath pk.seed honestEndpoints epoch
  let forgedLeaf := fun i =>
    hash.chain pk.seed epoch i (forgedWord i)
      (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i)
  (GXMSS.scheme hash enc K).Generated ProbCompRuntime.probComp (pk, sk) →
  GXMSS.Consistent hash pk sk →
  enc.value pk.seed forgedMessage forgedRandomizer epoch = some forgedWord →
  GXMSS.verify hash enc pk epoch forgedMessage
    ⟨forgedRandomizer, forgedOTS, forgedPath⟩ = true →
  hash.recoverRoot pk.seed epoch honestLeaf honestPath = pk.root →
  hash.recoverRoot pk.seed epoch forgedLeaf forgedPath = pk.root →
  (honestLeaf, honestPath) ≠ (forgedLeaf, forgedPath) →
  ∃ collision : Security.HashCollision T X,
    hash.findMerkleCollision pk.seed epoch honestLeaf forgedLeaf honestPath forgedPath =
      some collision ∧
    collision.Sound hash.thf pk.seed ∧
    (collision.tweak, collision.first) ∈
      hash.merkleOpeningQueries pk.seed epoch honestLeaf honestPath ∧
    (collision.tweak, collision.second) ∈
      hash.merkleOpeningQueries pk.seed epoch forgedLeaf forgedPath ∧
    ((honestLeaf ≠ forgedLeaf ∧
        collision = ⟨hash.treeTweak (0, epoch), hash.vectorInput honestLeaf,
          hash.vectorInput forgedLeaf⟩) ∨
      ∃ (z : Fin h) (u : H × H),
        collision = ⟨hash.treeTweak (Merkle.parentAddress epoch z),
          hash.pairInput (hash.honestMerkleChildren pk.seed honestEndpoints epoch z),
          hash.pairInput u⟩ ∧
        hash.honestMerkleChildren pk.seed honestEndpoints epoch z ≠ u)

/-- A generated-key, accepted forgery with a different complete raw opening yields the existing
computable honest-first Merkle collision. The statement includes raw-leaf and path-only
disagreement, and at height zero the `Fin h` branch is empty. It assumes neither unequal leaf
digests nor hash injectivity, a secret predecessor, or reduction challenge timing. -/
theorem ValidForgeryYieldsMerkleCollision [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h))
    (forgedMessage : M) (forgedRandomizer : R) (forgedWord : Codeword v (2 ^ w))
    (forgedOTS : Fin v → H) (forgedPath : Fin h → H) :
    ValidForgeryYieldsMerkleCollisionStatement hash enc K pk sk epoch forgedMessage
      forgedRandomizer forgedWord forgedOTS forgedPath := by
  unfold ValidForgeryYieldsMerkleCollisionStatement
  dsimp only
  intro _ _ _ _ hhonestRoot hforgedRoot hne
  have hroot : hash.recoverRoot pk.seed epoch (sk.endpoints epoch)
      (hash.authPath pk.seed sk.endpoints epoch) =
      hash.recoverRoot pk.seed epoch
        (fun i => hash.chain pk.seed epoch i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i)) forgedPath :=
    hhonestRoot.trans hforgedRoot.symm
  have hisSome := hash.findMerkleCollision_isSome pk.seed epoch
    (sk.endpoints epoch)
    (fun i => hash.chain pk.seed epoch i (forgedWord i)
      (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i))
    (hash.authPath pk.seed sk.endpoints epoch) forgedPath hne hroot
  obtain ⟨collision, hcollision⟩ := Option.isSome_iff_exists.mp hisSome
  have hsound := hash.findMerkleCollision_sound _ _ _ _ _ _ hcollision
  have hmem := hash.findMerkleCollision_mem_queries _ _ _ _ _ _ hcollision
  have hshape := hash.findMerkleCollision_honest_shape pk.seed sk.endpoints epoch _ _ hcollision
  exact ⟨collision, hcollision, hsound, hmem.1, hmem.2, hshape⟩

/-- A different complete opening to the honest root gives the exact registered challenge index
and a winning second input for the stand-alone Merkle target-collision game. -/
theorem merkleCollision_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (hv : 0 < v)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (ep : Fin (2 ^ h)) (forgedLeaf : Fin v → H) (forgedPath : Fin h → H)
    (hne : ((GXMSS.endpoints hash pp starts) ep,
      hash.authPath pp (GXMSS.endpoints hash pp starts) ep) ≠ (forgedLeaf, forgedPath))
    (hroot : hash.recoverRoot pp ep forgedLeaf forgedPath =
      hash.merkleRoot pp (GXMSS.endpoints hash pp starts)) :
    ∃ collision : Security.HashCollision T X,
      hash.findMerkleCollision pp ep ((GXMSS.endpoints hash pp starts) ep)
        forgedLeaf (hash.authPath pp (GXMSS.endpoints hash pp starts) ep) forgedPath =
          some collision ∧
      let history := Reductions.endpointTargets hash pp starts ++
        Reductions.merkleTargets hash pp (GXMSS.endpoints hash pp starts)
      let j := Reductions.registeredIndex history collision.tweak collision.first
      j < history.length ∧ history[j]? = some (collision.tweak, collision.first) ∧
        j < (Reductions.merkleTCRProblem hash).numTargets ∧
        decide (collision.second ≠ collision.first ∧
          (HashInstance.thf hash).eval pp collision.tweak collision.second =
            (HashInstance.thf hash).eval pp collision.tweak collision.first) = true := by
  have hisSome := hash.findMerkleCollision_isSome_of_honest pp
    (GXMSS.endpoints hash pp starts) ep forgedLeaf forgedPath hne hroot
  obtain ⟨collision, hcollision⟩ := Option.isSome_iff_exists.mp hisSome
  have hsound := hash.findMerkleCollision_sound pp ep _ _ _ _ hcollision
  have hmem := (hash.findMerkleCollision_mem_queries pp ep _ _ _ _ hcollision).1
  have hspec := Reductions.merkleOpeningTarget_registeredIndex_spec
    hash pp starts (GXMSS.endpoints hash pp starts) ep
    (collision.tweak, collision.first) hmem
    (Reductions.merkleTCRProblem hash).numTargets (by
      simpa only [List.length_append, Reductions.endpointTargets_length,
        Reductions.merkleTargets_length] using
          Reductions.merkleProblem_capacity hash hv)
  refine ⟨collision, hcollision, ?_⟩
  dsimp only
  obtain ⟨hindex, hlookup, hcapacity⟩ := hspec
  refine ⟨hindex, hlookup, hcapacity, ?_⟩
  obtain ⟨hinputs, himage⟩ := hsound
  exact decide_eq_true (And.intro (Ne.symm hinputs) himage.symm)

private def merkleCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : Reductions.TCRKeyState PP T X H h v) (pp : PP)
    (out : Reductions.Result PP H M R h v) : ℕ × X :=
  let forgery := out.forgery
  let epoch := forgery.1
  let messageAndSignature := forgery.2
  let signature := messageAndSignature.2
  match Reductions.forgedLeaf? hash enc out with
  | none => (0, hash.vectorInput (state.endpoints 0))
  | some forgedLeaf =>
    match hash.findMerkleCollision pp epoch (state.endpoints epoch)
      forgedLeaf (hash.authPath pp state.endpoints epoch) signature.path with
    | none => (0, hash.vectorInput (state.endpoints 0))
    | some collision =>
      (Reductions.registeredIndex state.targets collision.tweak collision.first,
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
    (hdiff : Reductions.merkleDifferenceObservation hash enc K
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩ = true) :
    let endpoints := GXMSS.endpoints hash pp starts
    let registered := Reductions.endpointTargets hash pp starts ++
      Reductions.merkleTargets hash pp endpoints
    let state : Reductions.TCRKeyState PP T X H h v :=
      ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
    let out : Reductions.Result PP H M R h v :=
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩
    merkleCandidateWins hash pp registered (merkleCandidate hash enc state pp out) = true := by
  let endpoints := GXMSS.endpoints hash pp starts
  let registered := Reductions.endpointTargets hash pp starts ++
    Reductions.merkleTargets hash pp endpoints
  let state : Reductions.TCRKeyState PP T X H h v :=
    ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
  let out : Reductions.Result PP H M R h v :=
    ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
      forgery, history⟩
  let epoch := forgery.1
  let messageAndSignature := forgery.2
  let message := messageAndSignature.1
  let signature := messageAndSignature.2
  have hleaf : ∃ leaf, Reductions.forgedLeaf? hash enc out = some leaf := by
    cases h : Reductions.forgedLeaf? hash enc out with
    | none => simp [Reductions.merkleDifferenceObservation, out, h] at hdiff
    | some leaf => exact ⟨leaf, rfl⟩
  obtain ⟨leaf, hleaf⟩ := hleaf
  have hsplit := hdiff
  simp only [Reductions.merkleDifferenceObservation,
    Bool.and_eq_true] at hsplit
  have hne : (endpoints epoch, hash.authPath pp endpoints epoch) ≠
      (leaf, signature.path) := by
    let publicKey := out.pk
    let secretKey := out.sk
    have hne' := hsplit.2
    change (match Reductions.forgedLeaf? hash enc out with
      | none => false
      | some leaf => decide ((secretKey.endpoints epoch,
          hash.authPath publicKey.seed secretKey.endpoints epoch) ≠
        (leaf, signature.path))) = true at hne'
    rw [hleaf] at hne'
    simpa only [publicKey, secretKey, out, GXMSS.keys, endpoints] using
      (of_decide_eq_true hne')
  have hstrong : Reductions.sourceStrongObservation hash enc K out = true := by
    exact hsplit.1
  have hverify : GXMSS.verify hash enc (GXMSS.keys hash pp starts).1
      epoch message signature = true := by
    have hstrong' := hstrong
    simp only [Reductions.sourceStrongObservation,
      Reductions.sourceObservation,
      SyncSignatureUnforgeability.strongValid, GXMSS.scheme,
      Bool.and_eq_true] at hstrong'
    exact hstrong'.1
  obtain ⟨word, hword, hleafValue⟩ := Option.map_eq_some_iff.mp hleaf
  have hword' : enc.value pp message signature.randomizer epoch =
      some word := by
    simpa only [out, Reductions.forgedLeaf?, GXMSS.keys] using hword
  have hleafValue' : (fun i => hash.chain pp epoch i (word i)
      (2 ^ w - 1 - (word i).val) (signature.ots i)) = leaf := by
    simpa only [out, Reductions.forgedLeaf?, GXMSS.keys] using hleafValue
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
    (adv : Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let endpoints := GXMSS.endpoints hash pp starts
  let registered := Reductions.endpointTargets hash pp starts ++
    Reductions.merkleTargets hash pp endpoints
  let state : Reductions.TCRKeyState PP T X H h v :=
    ⟨starts, endpoints, hash.merkleRoot pp endpoints, registered, fallback⟩
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← Reductions.runWithKeys hash enc K adv pk sk
  pure (merkleCandidateWins hash pp registered (merkleCandidate hash enc state pp out))

private def merkleCoupledDifferenceProgram [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← Reductions.runWithKeys hash enc K adv pk sk
  pure (Reductions.merkleDifferenceObservation hash enc K out)

/-- The extra private fallback draw is lossless and invisible to the source difference
observation, so it preserves the full native Boolean measure. -/
private theorem merkleCoupledDifference_evalDist_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    𝒟[merkleCoupledDifferenceProgram hash enc K adv] =
      𝒟[Reductions.merkleDifferenceObservation hash enc K <$>
        Reductions.sourceProgram hash enc K adv] := by
  unfold merkleCoupledDifferenceProgram Reductions.sourceProgram GXMSS.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.keys, bind_assoc, Function.comp_def] using
    (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H)
      (do
        let starts ← GXMSS.sampleStarts H h v
        let (pk, sk) := GXMSS.keys hash pp starts
        let out ← Reductions.runWithKeys hash enc K adv pk sk
        pure (Reductions.merkleDifferenceObservation hash enc K out)))

/-- The authoritative Merkle TCR experiment is the faithful coupled execution, including its
private fallback draw and exact ordered challenge history. -/
private theorem merkleExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (adv : Reductions.SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (Reductions.merkleTargetCollisionReduction hash enc K hv adv) =
        merkleCoupledProgram hash enc K adv := by
  have hcap := Reductions.merkleProblem_capacity hash hv
  unfold SM_DT_TCR_Experiment merkleCoupledProgram
  simp only [Reductions.merkleTargetCollisionReduction]
  have hsetup (pp : PP) :
      (simulateQ (SM_DT_TCR_oracles (Reductions.merkleTCRProblem hash) pp)
        (Reductions.tcrKeySetup hash
          (2 * (2 ^ h) * v * (2 ^ w)))).run ([], []) = (do
          let fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let endpoints := GXMSS.endpoints hash pp starts
          let registered := Reductions.endpointTargets hash pp starts ++
            Reductions.merkleTargets hash pp endpoints
          pure ((⟨starts, endpoints, hash.merkleRoot pp endpoints, registered,
              fallback⟩ : Reductions.TCRKeyState PP T X H h v),
            registered, ([] : List T))) := by
    change (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf
        (2 * (2 ^ h) * v * (2 ^ w))) pp)
      (Reductions.tcrKeySetup hash
        (2 * (2 ^ h) * v * (2 ^ w)))).run ([], []) = _
    exact Reductions.tcrKeySetup_run hash _ pp (by
      simpa only [Reductions.merkleTCRProblem,
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
  cases hleaf : Reductions.forgedLeaf? hash enc out with
  | none =>
    simp only [merkleCandidate, merkleCandidateWins, hleaf,
      Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
      pure_bind, List.length_append, Reductions.endpointTargets_length,
      Reductions.merkleTargets_length, add_pos_iff,
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
        Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
        pure_bind, List.length_append, Reductions.endpointTargets_length,
        Reductions.merkleTargets_length, add_pos_iff,
        CanonicallyOrderedAdd.mul_pos, Order.lt_two_iff, zero_le, pow_pos,
        true_and, tsub_pos_iff_lt, Nat.one_lt_two_pow_iff,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        Nat.one_lt_pow_iff, Std.le_refl, or_true, getElem?_pos,
        PFunctor.FreeM.pure_inj]
      exact tcrDecision_eq _ _ _
    | some collision =>
      dsimp only [epoch, signature, messageAndSignature, forgery] at hcollision
      simp only [merkleCandidate, merkleCandidateWins, hleaf, hcollision,
        Reductions.merkleTCRProblem, ne_eq, Bool.decide_and, decide_not,
        pure_bind]
      cases hlookup : (Reductions.endpointTargets hash pp starts ++
          Reductions.merkleTargets hash pp
            (GXMSS.endpoints hash pp starts))[
          Reductions.registeredIndex
            (Reductions.endpointTargets hash pp starts ++
              Reductions.merkleTargets hash pp
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
    (adv : Reductions.SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (out : Reductions.Result PP H M R h v)
    (hout : out ∈ support
      (Reductions.runWithKeys hash enc K adv pk sk)) :
    out.pk = pk ∧ out.sk = sk := by
  simp only [Reductions.runWithKeys, mem_support_bind_iff] at hout
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
    (hv : 0 < v) (adv : Reductions.SchemeAdversary PP H M R h v) :
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
    (Reductions.runWithKeys hash enc K adv
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
    by_cases hdiff : Reductions.merkleDifferenceObservation hash enc K
        ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
          forgery, history⟩ = true
    · have hwin := merkleCandidateWins_of_difference hash enc K hv pp starts
        fallback forgery history hdiff
      simp [hdiff, hwin]
    · have hfalse : Reductions.merkleDifferenceObservation hash enc K
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
        (Reductions.merkleTargetCollisionReduction hash enc K hv adv) +
      Reductions.gameOneAdvantage hash enc K adv
  rw [← Reductions.sourceStrongOutputMeasure_eq_strongUnforgeableExp]
  have hdiff : ProbCompRuntime.probComp.evalDist
        (Reductions.merkleDifferenceObservation hash enc K <$>
          Reductions.sourceProgram hash enc K adv) {true} ≤
      SM_DT_TCR_Advantage
        (Reductions.merkleTargetCollisionReduction hash enc K hv adv) := by
    rw [ProbCompRuntime.probComp_evalDist,
      ← merkleCoupledDifference_evalDist_eq_source]
    change 𝒟[merkleCoupledDifferenceProgram hash enc K adv] {true} ≤
      𝒟[SM_DT_TCR_Experiment
        (Reductions.merkleTargetCollisionReduction hash enc K hv adv)] {true}
    rw [merkleExperiment_eq_coupled]
    exact merkleCoupledDifference_le_win hash enc K hv adv
  calc
    _ ≤ Reductions.gameOneAdvantage hash enc K adv +
        ProbCompRuntime.probComp.evalDist
          (Reductions.merkleDifferenceObservation hash enc K <$>
            Reductions.sourceProgram hash enc K adv) {true} :=
      sourceStrongWinningMass_le_gameOne_add_merkleDifference hash enc K adv
    _ ≤ Reductions.gameOneAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (Reductions.merkleTargetCollisionReduction hash enc K hv adv) :=
      add_le_add_right hdiff _
    _ = _ := add_comm _ _

end

end GXMSS.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
import all HashSig.GXMSS.Security.Auxiliary.FullRangeInteraction
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.IntervalUnforgeability
import all HashSig.GXMSS.Security.IntervalUnforgeability
public import HashSig.GXMSS.Security.Reductions.CollisionBounds
import all HashSig.GXMSS.Security.Reductions.CollisionBounds
public import HashSig.GXMSS.Security.Reductions.Experiments
import all HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSecurity
import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSecurity
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
public import HashSig.GXMSS.Security.Reductions.Interval.ChainCollision
import all HashSig.GXMSS.Security.Reductions.Interval.ChainCollision
public import HashSig.GXMSS.Security.Reductions.Interval.ChainHybrid
import all HashSig.GXMSS.Security.Reductions.Interval.ChainHybrid
public import HashSig.GXMSS.Security.Reductions.Interval.FillerGames
import all HashSig.GXMSS.Security.Reductions.Interval.FillerGames
public import HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.Interval.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.Interval.MerkleGames
import all HashSig.GXMSS.Security.Reductions.Interval.MerkleGames
public import HashSig.GXMSS.Security.Reductions.TCRSimulation
import all HashSig.GXMSS.Security.Reductions.TCRSimulation

/-!
# Full-range primitive security correspondences

At the full interval, each concrete reduction preserves the complete-tree primitive experiment.
Whole returned-output laws transport PRE and both UD worlds before comparing advantages. The
final bounds retain separate exact chain-position and power-of-two coefficients.
-/

public section

namespace GXMSS.Interval.Reductions

open OracleComp OracleSpec GXMSS.IntervalMerkle GXMSS.Reductions SyncSignatureUnforgeability
    Encoding
open ENNReal

variable {PP T X H M R : Type} {h w v : ℕ}

private theorem intervalEncodingSigningOracle_full
    (P : HashInstance PP T X H h w v)
    (sk : GXMSS.Interval.SecretKey PP H h v (Interval.full h)) :
    intervalEncodingSigningOracle (M := M) (R := R) P (Interval.full h) sk =
      encodingSigningOracle (M := M) (R := R) P sk.complete := by
  funext q history
  rcases q with ⟨ep, msg⟩
  have hsignature : (GXMSS.Interval.signatureOfWord P (Interval.full h) sk ep :
      Codeword v (2 ^ w) × R → GXMSS.Signature R H h v) =
      GXMSS.signatureOfWord P sk.complete ep := by
    funext wr
    exact GXMSS.Interval.signatureOfWord_full P sk ep wr
  simp only [intervalEncodingSigningOracle, encodingSigningOracle,
    Epoch.isActive_full, ite_true, hsignature]
  rfl

private theorem intervalEncodingInnerImpl_full
    (P : HashInstance PP T X H h w v)
    (sk : GXMSS.Interval.SecretKey PP H h v (Interval.full h)) :
    intervalEncodingInnerImpl (M := M) (R := R) P (Interval.full h) sk =
      encodingGameInnerImpl (M := M) (R := R) P sk.complete := by
  simp only [intervalEncodingInnerImpl, encodingGameInnerImpl,
    intervalEncodingSigningOracle_full]

private theorem encodingTargetCollisionReduction_full [SampleableType H] [SampleableType R]
     (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    encodingTargetCollisionReduction P enc qs K (Interval.full h) A =
      GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A := by
  unfold encodingTargetCollisionReduction GXMSS.Reductions.encodingTargetCollisionReduction
  congr 1
  funext pp
  simp only [GXMSS.IntervalMerkle.sampleFillers_full, OracleComp.liftComp_pure, pure_bind,
    intervalEncodingInnerImpl_full]
  apply bind_congr
  intro starts
  have hkeys := GXMSS.Interval.keys_full_project P pp starts (fun x => isEmptyElim x)
  simp only [GXMSS.Interval.projectSecret] at hkeys
  have hpk := congrArg Prod.fst hkeys
  have hsk := congrArg Prod.snd hkeys
  dsimp only at hpk hsk
  simp only [hpk, hsk, encodingGameInnerImpl]
  dsimp only [Forgery]

/-- The full-range encoding experiment equals the complete-tree encoding experiment for every
adversary output, without a source-event guard or signing-query premise. -/
private theorem encodingTargetCollisionExperiment_full [SampleableType H] [SampleableType R]
     [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    TargetCollisionResistance.experiment
      (encodingTargetCollisionReduction P enc qs K (Interval.full h) A) =
    TargetCollisionResistance.experiment
      (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) := by
  rw [encodingTargetCollisionReduction_full]

end GXMSS.Interval.Reductions

namespace GXMSS.Interval.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle Encoding ENNReal
open GXMSS.Reductions GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability

variable {PP T X H M R : Type} {h w v : ℕ}

open GXMSS.Unforgeability GXMSS.Interval.Reductions

/-- The full-range encoding reduction preserves the complete-tree encoding experiment. -/
theorem encodingTargetCollisionExperiment_full
    [SampleableType H] [SampleableType R]
     [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (A : SchemeAdversary PP H M R h v) :
    TargetCollisionResistance.experiment
      (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K (Interval.full h) A) =
    TargetCollisionResistance.experiment
      (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) := by
  exact GXMSS.Interval.Reductions.encodingTargetCollisionExperiment_full P enc qs K A

private theorem intervalSelectedChainObservation_full
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (fillers : Fillers (Interval.full h) H) (guess : Guess h w v)
    (out : Result PP H M R h v) :
    intervalSelectedChainObservation P enc K (Interval.full h) fillers guess out =
      GXMSS.Reductions.jointChainObservation P enc K (guess, out) := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  have hstrong : strongValid (GXMSS.Interval.scheme P enc K (Interval.full h))
      (pk, (epoch, message, signature), history) =
      strongValid (GXMSS.scheme P enc K) (pk, (epoch, message, signature), history) := rfl
  cases hs : history epoch with
  | none =>
    cases hw : enc.value pk.seed message signature.randomizer epoch <;>
      simp [intervalSelectedChainObservation, intervalChainRemainderObservation,
        intervalSelectedCut, activeMatchingEvent, intervalEncodingCollision,
        GXMSS.Reductions.jointChainObservation, gameFourObservation, gameThreeObservation,
          gameTwoObservation,
        gameOneObservation, forgedLeaf?, forgedEpochSource, designatedCutHolds, hs, hw,
        hstrong, GXMSS.IntervalMerkle.authPath_full, Epoch.isActive_full]; rfl
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none =>
      cases hw : enc.value pk.seed message signature.randomizer epoch <;>
        simp [intervalSelectedChainObservation, intervalChainRemainderObservation,
          intervalSelectedCut, activeMatchingEvent, intervalEncodingCollision,
          GXMSS.Reductions.jointChainObservation, gameFourObservation, gameThreeObservation,
            gameTwoObservation,
          gameOneObservation, forgedLeaf?, forgedEpochSource, designatedCutHolds, hs, hw,
          hstrong, GXMSS.IntervalMerkle.authPath_full, Epoch.isActive_full]; rfl
    | some honest =>
      cases hh : enc.value pk.seed first honest.randomizer epoch <;>
        cases hf : enc.value pk.seed message signature.randomizer epoch <;>
        simp [intervalSelectedChainObservation, intervalChainRemainderObservation,
          intervalSelectedCut, activeMatchingEvent, intervalEncodingCollision,
          GXMSS.Reductions.jointChainObservation, gameFiveObservation, gameFourObservation,
            gameThreeObservation,
          gameTwoObservation, gameOneObservation, forgedLeaf?, forgedEpochSource,
          designatedCutHolds, hs, hh, hf, hstrong, GXMSS.IntervalMerkle.authPath_full,
          Epoch.isActive_full, Bool.and_assoc, Bool.or_comm]; rfl

private def activeSelectorFullEquiv (h w v : ℕ) : ActiveSelector (Interval.full h) w v ≃
    Guess h w v where
  toFun := activeGuess (Interval.full h)
  invFun guess := (activeOffset (Interval.full h) (guessedEpoch guess)
    (Epoch.isActive_full _), guessedChain guess, guessedPosition guess)
  left_inv selector := activeGuess_injective (Interval.full h)
    (activeGuess_offset (Interval.full h) _ _ _ _)
  right_inv guess := by
    rcases guess with ⟨epoch, chain, position⟩
    exact activeGuess_offset (Interval.full h) epoch (Epoch.isActive_full epoch) chain position

private theorem uniformActiveSelector_full_bind [NeZero v] [NeZero (2 ^ w - 1)]
    (next : Guess h w v → ProbComp Bool) :
    letI : NeZero (((Interval.full h).last : ℕ) - ((Interval.full h).first : ℕ) + 1) := ⟨by omega⟩
    𝒟[do
      let selector ← ($ᵗ (ActiveSelector (Interval.full h) w v))
      next (activeGuess (Interval.full h) selector)] =
      𝒟[($ᵗ (Guess h w v) : ProbComp (Guess h w v)) >>= next] := by
  let : NeZero (((Interval.full h).last : ℕ) - ((Interval.full h).first : ℕ) + 1) := ⟨by omega⟩
  have hm := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (activeSelectorFullEquiv h w v).bijective
  simpa only [bind_map_left, Function.comp_def, activeSelectorFullEquiv, Equiv.coe_fn_mk]
    using (hm.bind_left next).evalDist_eq

private theorem intervalChainContext_full
    (P : HashInstance PP T X H h w v) (fillers : Fillers (Interval.full h) H) :
    intervalChainContext P (Interval.full h) fillers = completeChainContext P := by
  unfold intervalChainContext completeChainContext
  congr 1
  · funext epoch
    exact decide_eq_true (Epoch.isActive_full epoch)
  · funext pp endpoints
    exact GXMSS.IntervalMerkle.root_full P pp endpoints fillers
  · funext pp endpoints epoch
    exact GXMSS.IntervalMerkle.authPath_full P pp endpoints fillers epoch

private theorem fixedFallbackPreimageWitness_full
    [SampleableType H] [SampleableType R] [NeZero v]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (fillers : Fillers (Interval.full h) H) (guess : Guess h w v)
    (starts : Epoch h → Fin v → H) (out : Result PP H M R h v) :
    extractChainPreimageWithFallback P enc K (Interval.full h) fillers guess (starts 0 0) out =
      GXMSS.Reductions.jointPreimageWitness P enc K guess starts out := by
  unfold extractChainPreimageWithFallback GXMSS.Reductions.jointPreimageWitness
  rw [intervalSelectedChainObservation_full]
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history⟩
  cases hs : history epoch with
  | none => simp only [forgedEpochSource, hs]; rfl
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp only [forgedEpochSource, hs]; rfl
    | some honest =>
      simp only [forgedEpochSource, hs]
      cases hh : enc.value pk.seed first honest.randomizer epoch with
      | none => rfl
      | some honestWord =>
        cases hf : enc.value pk.seed message signature.randomizer epoch with
        | none => rfl
        | some forgedWord =>
          dsimp only
          cases GXMSS.Security.findSmallerCoordinate honestWord forgedWord <;> rfl

/-- Fixed-fallback interval chain PRE at full range has the complete primitive's native
Boolean measure. The proof transports the actual selector and original digest hidden-input laws,
the complete adaptive view, and every fallback output. -/
theorem chainPreimageExperiment_full
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    𝒟[SM_DT_PRE_Experiment
      (chainPreimageReduction P enc K (Interval.full h) hv hw A)] =
      𝒟[SM_DT_PRE_Experiment (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A)] := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : NeZero (((Interval.full h).last : ℕ) - ((Interval.full h).first : ℕ) + 1) := ⟨by omega⟩
  rw [fixedFallbackPREExperiment_eq_explicit P enc K (Interval.full h) hv hw A,
    GXMSS.Reductions.jointPREExperiment_eq_explicit P enc K hv hw A]
  unfold fixedFallbackPREExplicitProgram GXMSS.Reductions.jointPREExplicitProgram
  apply evalDist_bind_congr
  intro pp
  let kernel (guess : Guess h w v) (starts : Epoch h → Fin v → H) (hidden : H) :
      ProbComp Bool := do
    let tweak := P.chainTweak (guessedEpoch guess, guessedChain guess, guessedPosition guess)
    let answer := TweakableHash.eval P.thf pp tweak (P.digestInput hidden)
    let out ← runSpliced P enc K A pp guess answer starts
    pure (decide (TweakableHash.eval P.thf pp tweak
      (P.digestInput (GXMSS.Reductions.jointPreimageWitness P enc K guess starts out)) = answer))
  let next (guess : Guess h w v) : ProbComp Bool := do
    let starts ← GXMSS.sampleStarts H h v
    let hidden ← ($ᵗ H : ProbComp H)
    kernel guess starts hidden
  calc
    _ = 𝒟[do
        let selector ← ($ᵗ (ActiveSelector (Interval.full h) w v))
        next (activeGuess (Interval.full h) selector)] := by
      apply evalDist_bind_congr
      intro selector
      dsimp only [next]
      apply evalDist_bind_congr
      intro starts
      simp only [sampleFillers_full, pure_bind]
      simp only [fixedFallbackPreimageWitness_full, intervalChainContext_full]
      rfl
    _ = 𝒟[do let guess ← ($ᵗ (Guess h w v)); next guess] := uniformActiveSelector_full_bind next
    _ = _ := by simp only [next, kernel]

/-- Full-range original chain UD preserves both complete primitive worlds. The selector law,
original response law and complete adaptive view are transported before observing any bit. -/
theorem chainUndetectabilityExperiment_full
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v)
    (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world
      (GXMSS.Interval.Reductions.Chain.chainUndetectabilityReduction P enc K (Interval.full h) hv hw
          A)] =
      𝒟[SM_DT_UD_Experiment world
        (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A)] := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : NeZero (((Interval.full h).last : ℕ) - ((Interval.full h).first : ℕ) + 1) := ⟨by omega⟩
  rw [chainUDExperiment_eq_explicit P enc K (Interval.full h) hv hw A world,
    GXMSS.Reductions.jointUDExperiment_eq_explicit P enc K hv hw A world]
  unfold chainUDExplicitProgram GXMSS.Reductions.jointUDExplicitProgram
  apply evalDist_bind_congr
  intro pp
  let kernel (guess : Guess h w v) (j : Fin (2 ^ w - 1))
      (starts : Epoch h → Fin v → H) (answer : H) : ProbComp Bool :=
    if j.val < (guessedPosition guess).val then do
      let splice : Guess h w v := (guessedEpoch guess, guessedChain guess, j)
      let out ← runSpliced P enc K A pp splice answer starts
      pure (GXMSS.Reductions.jointChainObservation P enc K (guess, out))
    else pure false
  let next (guess : Guess h w v) : ProbComp Bool := do
    let j ← ($ᵗ (Fin (2 ^ w - 1)))
    let starts ← GXMSS.sampleStarts H h v
    let answer ← SM_DT_UD_response world (chainUDProblem P) pp
      (P.chainTweak (guessedEpoch guess, guessedChain guess, j))
    kernel guess j starts answer
  calc
    _ = 𝒟[do
        let selector ← ($ᵗ (ActiveSelector (Interval.full h) w v))
        next (activeGuess (Interval.full h) selector)] := by
      apply evalDist_bind_congr
      intro selector
      dsimp only [next]
      apply evalDist_bind_congr
      intro j
      apply evalDist_bind_congr
      intro starts
      simp only [sampleFillers_full, pure_bind]
      simp_rw [intervalChainContext_full, intervalSelectedChainObservation_full]
      rfl
    _ = 𝒟[do let guess ← ($ᵗ (Guess h w v)); next guess] := uniformActiveSelector_full_bind next
    _ = _ := by simp only [next, kernel]

private theorem prunedTargetRun_full_interval
    (P : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers (Interval.full h) H)
    (fallback : H) (z t : ℕ) :
    prunedTargetRun P (Interval.full h) pp endpoints fillers fallback z t =
      merkleTargetRun P pp endpoints fallback z t := by
  induction z generalizing t with
  | zero => simp [prunedTargetRun, merkleTargetRun, Subtree.full_not_isInactiveFrontier]
  | succ z ih =>
      simp only [prunedTargetRun, merkleTargetRun, Subtree.full_not_isInactiveFrontier,
        dite_false, ih]

private theorem prunedTargets_full_interval
    (P : HashInstance PP T X H h w v) (pp : PP)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers (Interval.full h) H) :
    prunedTargets P (Interval.full h) pp endpoints fillers = merkleTargets P pp endpoints := by
  unfold prunedTargets merkleTargets
  rw [prunedTargetRun_full_interval]

/-- The full-range Merkle experiment equals the complete-tree experiment, including fallback
outputs. -/
theorem merkleTargetCollisionExperiment_full [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) :
    SM_DT_TCR_Experiment (merkleTargetCollisionAdversary P enc K (Interval.full h) hv A) =
      SM_DT_TCR_Experiment (merkleTargetCollisionReduction P enc K hv A) := by
  rw [merkleExperiment_eq_coupledWin P enc K (Interval.full h) hv A,
    GXMSS.Unforgeability.merkleExperiment_eq_coupled P enc K hv A]
  unfold coupledMerkleWin GXMSS.Unforgeability.merkleCoupledProgram
  apply bind_congr
  intro pp
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  simp only [sampleFillers_full, pure_bind, prunedTargets_full_interval,
    GXMSS.IntervalMerkle.root_full]
  simp only [GXMSS.Interval.viewWithKeys, runWithKeys, bind_assoc,
    GXMSS.Interval.keys, GXMSS.keys, GXMSS.Interval.signingOracle_full,
    GXMSS.Interval.projectSecret, pure_bind]
  dsimp only [SyncSignatureUnforgeability.ExperimentResult,
    SyncSignatureUnforgeability.Forgery]
  simp only [GXMSS.IntervalMerkle.root_full, pure_bind]
  apply bind_congr
  rintro ⟨⟨e, msg, sig⟩, history⟩
  simp only [intervalMerkleCandidate, GXMSS.Unforgeability.merkleCandidate,
    forgedLeaf?, Epoch.isActive_full, ite_true, authPath_full]
  cases enc.value pp msg sig.randomizer e <;> rfl


/-- The full-range Merkle reduction has the complete-tree target-collision advantage. -/
theorem merkleTargetCollisionAdvantage_full [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : Encoding.IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) :
    SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K (Interval.full h) hv A) =
      SM_DT_TCR_Advantage (merkleTargetCollisionReduction P enc K hv A) := by
  unfold SM_DT_TCR_Advantage
  rw [merkleTargetCollisionExperiment_full]

/-- Full range preserves the complete same-message/randomizer chain collision experiment. -/
theorem sameMessageRandomizerChainTargetCollisionExperiment_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (A : SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction
        P enc K (Interval.full h) A) =
    SM_DT_TCR_Experiment
      (GXMSS.Reductions.firstChainTargetCollisionReduction P enc K A) := by
  rw [GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainExperiment_eq_coupled,
    GXMSS.Unforgeability.firstChainExperiment_eq_coupled]
  unfold GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainCoupledProgram
    GXMSS.Unforgeability.firstChainCoupledProgram
  apply bind_congr
  intro pp
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  simp only [sampleFillers_full, pure_bind]
  simp only [GXMSS.Interval.viewFromKeys, GXMSS.Interval.viewWithKeys, runWithKeys, bind_assoc,
    GXMSS.Interval.keys, GXMSS.keys, GXMSS.IntervalMerkle.root_full,
        GXMSS.Interval.signingOracle_full,
    GXMSS.Interval.projectSecret, pure_bind]
  dsimp only [ExperimentResult, Forgery]
  apply bind_congr
  rintro ⟨⟨epoch, message, signature⟩, history⟩
  rfl

/-- Full range preserves the complete chain-cut target-collision experiment. -/
theorem chainCutTargetCollisionExperiment_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (A : SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K (Interval.full h) A)
          =
    SM_DT_TCR_Experiment
      (GXMSS.Reductions.secondChainTargetCollisionReduction P enc K A) := by
  rw [GXMSS.Interval.Reductions.Chain.chainCutExperiment_eq_coupled,
    GXMSS.Unforgeability.secondChainExperiment_eq_coupled]
  unfold GXMSS.Interval.Reductions.Chain.chainCutCoupledProgram
    GXMSS.Unforgeability.secondChainCoupledProgram
  apply bind_congr
  intro pp
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  simp only [sampleFillers_full, pure_bind]
  simp only [GXMSS.Interval.viewFromKeys, GXMSS.Interval.viewWithKeys, runWithKeys, bind_assoc,
    GXMSS.Interval.keys, GXMSS.keys, GXMSS.IntervalMerkle.root_full,
        GXMSS.Interval.signingOracle_full,
    GXMSS.Interval.projectSecret, pure_bind]
  dsimp only [ExperimentResult, Forgery]
  apply bind_congr
  rintro ⟨⟨epoch, message, signature⟩, history⟩
  rfl

/-- Whole original-domain PRE laws imply equality of the actual advantages at full range. -/
theorem chainPreimageAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_PRE_Advantage (chainPreimageReduction P enc K (Interval.full h) hv hw A) =
      SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A) := by
  exact congrArg (fun d : MeasureTheory.Measure Bool => d {true})
    (chainPreimageExperiment_full P enc K hv hw A)

/-- Equality of both whole original-domain UD laws preserves Boolean distance at full range. -/
theorem chainUndetectabilityAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K (Interval.full h) hv hw A) =
      SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A) := by
  unfold SM_DT_UD_Advantage
  rw [chainUndetectabilityExperiment_full, chainUndetectabilityExperiment_full]

/-- The full-range sharp bound retains the exact positive-position coefficients and complete-tree
primitive advantages. Empty frontier families contribute no tickets; chain terms remain. -/
theorem strongUnforgeabilityBound_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    strongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction P enc K hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction P enc K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction P enc K A) +
      (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A) +
      (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A) := by
  unfold strongUnforgeabilityBound
  simp only [GXMSS.Interval.activeChainPositionCount_full, GXMSS.Interval.Filler.udAdvantage_full,
    GXMSS.Interval.Filler.preAdvantage_full, add_zero]
  rw [chainPreimageAdvantage_full, chainUndetectabilityAdvantage_full]
  simp only [SM_DT_TCR_Advantage, TargetCollisionResistance.advantage,
    TargetCollisionResistance.outputMeasure, merkleTargetCollisionExperiment_full,
    encodingTargetCollisionExperiment_full,
      sameMessageRandomizerChainTargetCollisionExperiment_full,
    chainCutTargetCollisionExperiment_full]
  push_cast
  ring

/-- The full-range power-of-two bound equals the complete-tree reduction expression by
primitive experiment equalities and coefficient rewriting. -/
theorem powerOfTwoStrongUnforgeabilityBound_full
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    powerOfTwoStrongUnforgeabilityBound P enc K qs (Interval.full h) hv hw A =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction P enc K hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction P enc qs K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction P enc K A) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction P enc K A) +
      (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) *
        (((2 ^ w : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction P enc K hv hw A) +
          SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction P enc K hv hw A)) := by
  unfold powerOfTwoStrongUnforgeabilityBound
  rw [Interval.length_full]
  simp only [GXMSS.Interval.Filler.udAdvantage_full, GXMSS.Interval.Filler.preAdvantage_full,
      add_zero]
  rw [chainPreimageAdvantage_full, chainUndetectabilityAdvantage_full]
  simp only [SM_DT_TCR_Advantage, TargetCollisionResistance.advantage,
    TargetCollisionResistance.outputMeasure, merkleTargetCollisionExperiment_full,
    encodingTargetCollisionExperiment_full,
      sameMessageRandomizerChainTargetCollisionExperiment_full,
    chainCutTargetCollisionExperiment_full]
  push_cast
  ring

end GXMSS.Interval.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Security.Reductions.SecondChainCollision
public import HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision
public import HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision
import all HashSig.GXMSS.Security.Reductions.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.FirstChainCollision
import all HashSig.GXMSS.Security.Reductions.SecondChainCollision
import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.GuessingGames
import all HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.SplicedChain
import all HashSig.GXMSS.Security.Reductions.ChainHybrid
import all HashSig.GXMSS.Security.Reductions.JointReductions

/-!
# Strong unforgeability reduction bound

The separate-term inequality for Theorem 1 in ePrint 2025/055 combines the Merkle,
encoding and two chain target-collision hops with one joint UD/PRE charge. It assumes
two distinct global codewords. The unrestricted bound, paper coefficient-two comparison,
footnote 11, source-query admissibility and reduction resource bounds remain open.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``ValidForgeryYieldsMerkleCollision
  let env ← Lean.getEnv
  let info? : Option Lean.ConstantInfo := env.find? name
  let some (.thmInfo info) := info?
    | throwError "{name} is not a theorem defined in this module"
  Lean.Meta.forallTelescope info.type fun fvars result => do
    let levelParams := info.levelParams
    let levels := levelParams.map Lean.Level.param
    let expected := Lean.mkAppN (Lean.mkConst ``ValidForgeryYieldsMerkleCollisionStatement levels)
      fvars
    unless (← Lean.Meta.isDefEq result expected) do
      throwError "{name} does not have the exact named Merkle-forgery proposition"
    let resultType ← Lean.Meta.inferType result
    unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
      throwError "{name} is not a universally closed proposition"
  let axioms ← Lean.collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter fun ax => !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "unapproved transitive axioms for {name}: {unexpected.toList}"

/-- The successful-record Game 1 to Game 2 hop using the fixed target-collision reduction.
The pathwise signing bound counts repeated and failed queries. The inequality compares returned
native mass without conditioning on termination or on successful retries. -/
@[expose]
def SuccessfulEncodingTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) : Prop :=
  SigningQueryBound qs adv →
    Reductions.gameOneAdvantage hash enc K adv ≤
      Reductions.gameTwoAdvantage hash enc K adv +
        Encoding.TargetCollisionResistance.advantage
          (Reductions.encodingTargetCollisionReduction hash enc qs K adv)

/-- Returned Game 1 wins lost at Game 2 are charged to the successful recorded encoding target
in the authoritative collision game. -/
theorem successful_encoding_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    SuccessfulEncodingTargetCollisionBound hash enc qs K adv := by
  intro hbound
  exact (Reductions.gameOneAdvantage_le_gameTwo_add_successfulDifference
    hash enc K adv).trans (add_le_add_right
      (Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
        hash enc qs K adv hbound) _)

set_option maxHeartbeats 800000 in
-- Elaborating the six concrete adversary types through the existing reduction-bound interface
-- exceeds the default heartbeat limit; the proof itself is a finite chain of inequalities.
/-- The separate-term strong-unforgeability reduction for a global code containing two distinct
words. The premise supplies the non-maximum output property needed by the single-selector
accounting. The unrestricted `StrongUnforgeabilityReductionBound` remains a proposition. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    StrongUnforgeabilityReductionBound hash enc K qs adv
      (Reductions.merkleTargetCollisionReduction hash enc K hv adv)
      (Reductions.encodingTargetCollisionReduction hash enc qs K adv)
      (Reductions.firstChainTargetCollisionReduction hash enc K adv)
      (Reductions.secondChainTargetCollisionReduction hash enc K adv)
      (Reductions.jointUndetectabilityReduction hash enc K hv hw adv)
      (Reductions.jointPreimageReduction hash enc K hv hw adv) := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  have hnonmax := Reductions.noMaximumOutput_of_two_codewords enc htwo
  intro hqueries
  have hmerkle := first_merkle_target_collision_bound hash enc K hv adv
  have hencoding := successful_encoding_target_collision_bound hash enc qs K adv hqueries
  have hfirst := game_two_le_game_three_add_first_chain_target_collision hash enc K adv
  have hsecond := game_three_le_game_four_add_second_chain_target_collision hash enc K adv
  have hjoint := Reductions.jointChainAdvantage_le_jointUD_add_jointPRE
    hash enc K hv hw adv
  have hgameFour : Reductions.gameFourAdvantage hash enc K adv ≤
      (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
        ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (Reductions.jointPreimageReduction hash enc K hv hw adv)) := by
    rw [Reductions.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
      hash enc K hv hw adv hnonmax]
    gcongr
  have hcard : (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) ≤
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) := by
    exact_mod_cast Reductions.guess_cardinality_le_paper_coefficient h w v
  have hposition : (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) ≤ (↑(2 ^ w) : ℝ≥0∞) := by
    exact_mod_cast (Nat.sub_le (2 ^ w) 1)
  have hcharge : (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
        ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (Reductions.jointPreimageReduction hash enc K hv hw adv)) ≤
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (Reductions.jointPreimageReduction hash enc K hv hw adv)) := by
    gcongr
  let merkle := SM_DT_TCR_Advantage
    (Reductions.merkleTargetCollisionReduction hash enc K hv adv)
  let encoding := Encoding.TargetCollisionResistance.advantage
    (Reductions.encodingTargetCollisionReduction hash enc qs K adv)
  let first := SM_DT_TCR_Advantage
    (Reductions.firstChainTargetCollisionReduction hash enc K adv)
  let second := SM_DT_TCR_Advantage
    (Reductions.secondChainTargetCollisionReduction hash enc K adv)
  let ud := SM_DT_UD_Advantage
    (Reductions.jointUndetectabilityReduction hash enc K hv hw adv)
  let pre := SM_DT_PRE_Advantage
    (Reductions.jointPreimageReduction hash enc K hv hw adv)
  change SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp adv ≤
    merkle + encoding + first + second +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) * ((↑(2 ^ w) : ℝ≥0∞) * ud + pre)
  calc
    _ ≤ merkle + Reductions.gameOneAdvantage hash enc K adv := hmerkle
    _ ≤ merkle + (Reductions.gameTwoAdvantage hash enc K adv + encoding) :=
      add_le_add_right hencoding _
    _ = merkle + encoding + Reductions.gameTwoAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding +
        (Reductions.gameThreeAdvantage hash enc K adv + first) :=
      add_le_add_right hfirst _
    _ = merkle + encoding + first +
        Reductions.gameThreeAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding + first +
        (Reductions.gameFourAdvantage hash enc K adv + second) :=
      add_le_add_right hsecond _
    _ = merkle + encoding + first + second +
        Reductions.gameFourAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding + first + second +
        (Fintype.card (Reductions.Guess h w v) : ℝ≥0∞) *
          ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) * ud + pre) :=
      add_le_add_right hgameFour _
    _ ≤ merkle + encoding + first + second +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) * ud + pre) :=
      add_le_add_right hcharge _
    _ = _ := by ac_rfl

end

end GXMSS.Unforgeability

/-!
## Bounds for specific encodings

The checksum and target-sum bounds compose the generic theorem with the native encoding
target-collision bridges. Equality of public-seed samplers is explicit because the scheme
hash and encoding hash have different input and output types.
-/

namespace GXMSS.Unforgeability.SpecificEncoding

open GXMSS.Encoding
open GXMSS.Unforgeability
open GXMSS.Reductions
open OracleComp TweakableHash ENNReal

variable {PP T X H M R Y : Type} {h w v n₀ target : ℕ}

/-- Seed-sampler agreement identifies the scheme's encoding game with the bridge game. -/
theorem encoding_problem_eq [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (qs K : ℕ) (hseed : hash.thf.seedGen = bridge.th.seedGen) :
    encodingTCRProblem hash bridge.enc qs K =
      TargetCollisionReduction.encodingProblem bridge qs K := by
  simp [encodingTCRProblem, TargetCollisionReduction.encodingProblem, hseed]

private theorem advantage_eq_transport
    [DecidableEq M] [DecidableEq R]
    {P Q : TargetCollisionResistance.Problem PP M R (Fin (2 ^ h)) v (2 ^ w)}
    (heq : P = Q) (source : TargetCollisionResistance.Adversary P) :
    TargetCollisionResistance.advantage source =
      TargetCollisionResistance.advantage (heq ▸ source) := by
  cases heq
  rfl

/-- The hash-game adversary obtained from the scheme's encoding-game adversary. -/
@[expose] noncomputable def encodingHashTargetCollisionReduction
    [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :=
  TargetCollisionReduction.reduction bridge qs K
    ((encoding_problem_eq hash bridge qs K hseed) ▸
      encodingTargetCollisionReduction hash bridge.enc qs K adv)

set_option maxHeartbeats 800000 in
-- Elaborating the six scheme reductions and the dependent transport of the encoding adversary
-- through the seed-agreed target-collision problem exceeds the default heartbeat limit.
/-- A two-word encoding with a target-collision bridge yields a scheme bound in terms of the
encoding hash's SM-DT-rTCR advantage. The other generic GXMSS terms are unchanged. -/
theorem strong_unforgeability_bound_of_bridge
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (bridge : TargetCollisionReduction.Bridge PP M R (Fin (2 ^ h)) T Y v (2 ^ w))
    (hseed : hash.thf.seedGen = bridge.th.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ bridge.enc.code ∧ y ∈ bridge.enc.code ∧ x ≠ y)
    (adv : SchemeAdversary PP H M R h v)
    (hqueries : SigningQueryBound qs adv) :
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash bridge.enc K hv adv) +
        SM_DT_RTCR_Advantage (encodingHashTargetCollisionReduction hash bridge hseed qs K adv) +
        SM_DT_TCR_Advantage (firstChainTargetCollisionReduction hash bridge.enc K adv) +
        SM_DT_TCR_Advantage (secondChainTargetCollisionReduction hash bridge.enc K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage (jointUndetectabilityReduction hash bridge.enc K hv hw adv) +
            SM_DT_PRE_Advantage (jointPreimageReduction hash bridge.enc K hv hw adv)) := by
  let source := encodingTargetCollisionReduction hash bridge.enc qs K adv
  let source' := (encoding_problem_eq hash bridge qs K hseed) ▸ source
  have hcast : TargetCollisionResistance.advantage source =
      TargetCollisionResistance.advantage source' :=
    advantage_eq_transport (encoding_problem_eq hash bridge qs K hseed) source
  have hhash := TargetCollisionReduction.advantage_le_hash bridge qs K source'
  have hbase := (strong_unforgeability_reduction_bound
    hash bridge.enc K qs hv hw htwo adv) hqueries
  change SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.scheme hash bridge.enc K) ProbCompRuntime.probComp adv ≤
    SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash bridge.enc K hv adv) +
      TargetCollisionResistance.advantage source +
      SM_DT_TCR_Advantage (firstChainTargetCollisionReduction hash bridge.enc K adv) +
      SM_DT_TCR_Advantage (secondChainTargetCollisionReduction hash bridge.enc K adv) +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) *
            SM_DT_UD_Advantage (jointUndetectabilityReduction hash bridge.enc K hv hw adv) +
          SM_DT_PRE_Advantage (jointPreimageReduction hash bridge.enc K hv hw adv)) at hbase
  calc
    _ ≤ _ := hbase
    _ ≤ _ := by
      dsimp only [encodingHashTargetCollisionReduction]
      rw [hcast]
      gcongr

set_option maxHeartbeats 800000 in
-- The checksum code dimensions appear in all six concrete reduction types and require a larger
-- elaboration budget when the generic composition theorem is specialized.
/-- The checksum-word instance has two global codewords from its positive payload length and
digit width. Its scheme bound charges encoding collisions to the message hash's SM-DT-rTCR game. -/
theorem winternitz_strong_unforgeability_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword n₀ (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h (n₀ + Winternitz.checksumWidth n₀ w))]
    (hash : HashInstance PP T X H h w (n₀ + Winternitz.checksumWidth n₀ w))
    (params : Winternitz.Parameters PP M R (Fin (2 ^ h)) T n₀ w)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (adv : SchemeAdversary PP H M R h (n₀ + Winternitz.checksumWidth n₀ w)) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (Winternitz.encoding params) K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (Winternitz.encoding params) K
            (by have := params.payloadLengthPositive; omega :
              0 < n₀ + Winternitz.checksumWidth n₀ w) adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (WinternitzCollision.bridge params hEpoch)
            (by simpa [WinternitzCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (Winternitz.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (Winternitz.encoding params) K adv) +
        (↑((2 ^ h) * (n₀ + Winternitz.checksumWidth n₀ w) * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (Winternitz.encoding params) K
                  (by have := params.payloadLengthPositive; omega :
                    0 < n₀ + Winternitz.checksumWidth n₀ w)
                  params.digitWidthPositive adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (Winternitz.encoding params) K
                (by have := params.payloadLengthPositive; omega :
                  0 < n₀ + Winternitz.checksumWidth n₀ w)
                params.digitWidthPositive adv)) := by
  intro hqueries
  have hv : 0 < n₀ + Winternitz.checksumWidth n₀ w := by
    have := params.payloadLengthPositive
    omega
  have htwo : ∃ x y : Codeword (n₀ + Winternitz.checksumWidth n₀ w) (2 ^ w),
      x ∈ (WinternitzCollision.bridge params hEpoch).enc.code ∧
        y ∈ (WinternitzCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
    simpa only [WinternitzCollision.bridge, Winternitz.encoding] using
      Winternitz.two_codewords params
  exact strong_unforgeability_bound_of_bridge hash
    (WinternitzCollision.bridge params hEpoch)
    (by simpa [WinternitzCollision.bridge] using hseed) K qs hv
    params.digitWidthPositive htwo adv hqueries

set_option maxHeartbeats 800000 in
-- Specializing the generic scheme reduction to the target-sum bridge elaborates six concrete
-- adversary types and exceeds the default heartbeat limit.
/-- The target-sum scheme bound under the exact parameter-only condition that its finite code
contains at least two words. The returned sum-mismatch failure mass is retained. -/
theorem target_sum_strong_unforgeability_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (hcount : 2 ≤ TargetSum.acceptedCount v w target)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (TargetSum.encoding params) K hv adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (TargetSum.encoding params) K hv hw adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (TargetSum.encoding params) K hv hw adv)) := by
  intro hqueries
  have htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧
        y ∈ (TargetSumCollision.bridge params hEpoch).enc.code ∧ x ≠ y := by
    simpa only [TargetSumCollision.bridge, TargetSum.encoding] using
      TargetSum.two_codewords_of_acceptedCount v w target hcount
  exact strong_unforgeability_bound_of_bridge hash
    (TargetSumCollision.bridge params hEpoch)
    (by simpa [TargetSumCollision.bridge] using hseed) K qs hv hw htwo adv hqueries

/-- A positive target that fits in one digit, with at least two digit positions, directly
discharges the target-sum code-size premise in the scheme bound. -/
theorem target_sum_strong_unforgeability_bound_of_small_target
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Codeword v (2 ^ w))]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (params : TargetSum.Parameters PP M R (Fin (2 ^ h)) T v w target)
    (hEpoch : Function.Injective params.epochToTweak)
    (hseed : hash.thf.seedGen = params.thf.seedGen) (K qs : ℕ)
    (hv : 2 ≤ v) (hw : 0 < w) (htarget : 0 < target) (hfit : target < 2 ^ w)
    (adv : SchemeAdversary PP H M R h v) :
    SigningQueryBound qs adv →
    SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash (TargetSum.encoding params) K) ProbCompRuntime.probComp adv ≤
      SM_DT_TCR_Advantage
          (merkleTargetCollisionReduction hash (TargetSum.encoding params) K
            (by omega : 0 < v) adv) +
        SM_DT_RTCR_Advantage
          (encodingHashTargetCollisionReduction hash (TargetSumCollision.bridge params hEpoch)
            (by simpa [TargetSumCollision.bridge] using hseed) qs K adv) +
        SM_DT_TCR_Advantage
          (firstChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        SM_DT_TCR_Advantage
          (secondChainTargetCollisionReduction hash (TargetSum.encoding params) K adv) +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) *
              SM_DT_UD_Advantage
                (jointUndetectabilityReduction hash (TargetSum.encoding params) K
                  (by omega : 0 < v) hw adv) +
            SM_DT_PRE_Advantage
              (jointPreimageReduction hash (TargetSum.encoding params) K
                (by omega : 0 < v) hw adv)) := by
  exact target_sum_strong_unforgeability_bound hash params hEpoch hseed K qs
    (by omega : 0 < v) hw
    (TargetSum.acceptedCount_two_le_of_small_target v w target hv htarget hfit) adv

end GXMSS.Unforgeability.SpecificEncoding

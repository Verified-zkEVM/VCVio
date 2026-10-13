/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Security.Unforgeability.SecondChainCollision
import all HashSig.GXMSS.Security.Unforgeability.MerkleCollision
import all HashSig.GXMSS.Security.Unforgeability.FirstChainCollision
import all HashSig.GXMSS.Security.Unforgeability.SecondChainCollision
import all HashSig.GXMSS.Security.ReductionGames.SourceGames
import all HashSig.GXMSS.Security.ReductionGames.GuessingGames
import all HashSig.GXMSS.Security.ReductionGames.CollisionReductions
import all HashSig.GXMSS.Security.ReductionGames.SplicedChain
import all HashSig.GXMSS.Security.ReductionGames.ChainHybrid
import all HashSig.GXMSS.Security.ReductionGames.JointReductions

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
    (adv : ReductionGames.SchemeAdversary PP H M R h v) : Prop :=
  SigningQueryBound qs adv →
    ReductionGames.gameOneAdvantage hash enc K adv ≤
      ReductionGames.gameTwoAdvantage hash enc K adv +
        Encoding.TargetCollisionResistance.advantage
          (ReductionGames.encodingTargetCollisionReduction hash enc qs K adv)

/-- Returned Game 1 wins lost at Game 2 are charged to the successful recorded encoding target
in the authoritative collision game. -/
theorem successful_encoding_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    SuccessfulEncodingTargetCollisionBound hash enc qs K adv := by
  intro hbound
  exact (ReductionGames.gameOneAdvantage_le_gameTwo_add_successfulDifference
    hash enc K adv).trans (add_le_add_right
      (ReductionGames.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
        hash enc qs K adv hbound) _)

set_option maxHeartbeats 800000 in
-- Elaborating the six concrete adversary types through the existing reduction-bound interface
-- exceeds the default heartbeat limit; the proof itself is a finite chain of inequalities.
/-- The separate-term strong-unforgeability reduction for a global code containing two distinct
words. The premise supplies the non-maximum output property needed by the single-selector
accounting. The unrestricted `StrongUnforgeabilityReductionBound` remains a proposition. -/
theorem strong_unforgeability_reduction_bound_of_two_codewords
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
      (ReductionGames.merkleTargetCollisionReduction hash enc K hv adv)
      (ReductionGames.encodingTargetCollisionReduction hash enc qs K adv)
      (ReductionGames.firstChainTargetCollisionReduction hash enc K adv)
      (ReductionGames.secondChainTargetCollisionReduction hash enc K adv)
      (ReductionGames.jointUndetectabilityReduction hash enc K hv hw adv)
      (ReductionGames.jointPreimageReduction hash enc K hv hw adv) := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) := ⟨by
    have := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega⟩
  have hnonmax := ReductionGames.noMaximumOutput_of_two_codewords enc htwo
  intro hqueries
  have hmerkle := first_merkle_target_collision_bound hash enc K hv adv
  have hencoding := successful_encoding_target_collision_bound hash enc qs K adv hqueries
  have hfirst := game_two_le_game_three_add_first_chain_target_collision hash enc K adv
  have hsecond := game_three_le_game_four_add_second_chain_target_collision hash enc K adv
  have hjoint := ReductionGames.jointChainAdvantage_le_jointUD_add_jointPRE
    hash enc K hv hw adv
  have hgameFour : ReductionGames.gameFourAdvantage hash enc K adv ≤
      (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
        ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (ReductionGames.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (ReductionGames.jointPreimageReduction hash enc K hv hw adv)) := by
    rw [ReductionGames.gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
      hash enc K hv hw adv hnonmax]
    gcongr
  have hcard : (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) ≤
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) := by
    exact_mod_cast ReductionGames.guess_cardinality_le_paper_coefficient h w v
  have hposition : (↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) ≤ (↑(2 ^ w) : ℝ≥0∞) := by
    exact_mod_cast (Nat.sub_le (2 ^ w) 1)
  have hcharge : (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
        ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (ReductionGames.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (ReductionGames.jointPreimageReduction hash enc K hv hw adv)) ≤
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) *
            SM_DT_UD_Advantage
              (ReductionGames.jointUndetectabilityReduction hash enc K hv hw adv) +
          SM_DT_PRE_Advantage
              (ReductionGames.jointPreimageReduction hash enc K hv hw adv)) := by
    gcongr
  let merkle := SM_DT_TCR_Advantage
    (ReductionGames.merkleTargetCollisionReduction hash enc K hv adv)
  let encoding := Encoding.TargetCollisionResistance.advantage
    (ReductionGames.encodingTargetCollisionReduction hash enc qs K adv)
  let first := SM_DT_TCR_Advantage
    (ReductionGames.firstChainTargetCollisionReduction hash enc K adv)
  let second := SM_DT_TCR_Advantage
    (ReductionGames.secondChainTargetCollisionReduction hash enc K adv)
  let ud := SM_DT_UD_Advantage
    (ReductionGames.jointUndetectabilityReduction hash enc K hv hw adv)
  let pre := SM_DT_PRE_Advantage
    (ReductionGames.jointPreimageReduction hash enc K hv hw adv)
  change SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc K)
      ProbCompRuntime.probComp adv ≤
    merkle + encoding + first + second +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) * ((↑(2 ^ w) : ℝ≥0∞) * ud + pre)
  calc
    _ ≤ merkle + ReductionGames.gameOneAdvantage hash enc K adv := hmerkle
    _ ≤ merkle + (ReductionGames.gameTwoAdvantage hash enc K adv + encoding) :=
      add_le_add_right hencoding _
    _ = merkle + encoding + ReductionGames.gameTwoAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding +
        (ReductionGames.gameThreeAdvantage hash enc K adv + first) :=
      add_le_add_right hfirst _
    _ = merkle + encoding + first +
        ReductionGames.gameThreeAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding + first +
        (ReductionGames.gameFourAdvantage hash enc K adv + second) :=
      add_le_add_right hsecond _
    _ = merkle + encoding + first + second +
        ReductionGames.gameFourAdvantage hash enc K adv := by ac_rfl
    _ ≤ merkle + encoding + first + second +
        (Fintype.card (ReductionGames.Guess h w v) : ℝ≥0∞) *
          ((↑(2 ^ w - 1 : ℕ) : ℝ≥0∞) * ud + pre) :=
      add_le_add_right hgameFour _
    _ ≤ merkle + encoding + first + second +
        (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
          ((↑(2 ^ w) : ℝ≥0∞) * ud + pre) :=
      add_le_add_right hcharge _
    _ = _ := by ac_rfl

end

end GXMSS.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.FrontierCount
import all HashSig.GXMSS.Interval.FrontierCount
public import HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets
import all HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets
public import HashSig.GXMSS.Security.Reductions.CollisionBounds
import all HashSig.GXMSS.Security.Reductions.CollisionBounds
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
import all HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
import all HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
import all HashSig.GXMSS.Security.Interval.Reductions.SourcePartition

/-!
# Strong unforgeability of inclusive interval GXMSS

The native source partition is composed with addressed-hash collision and original-domain
chain/frontier
reductions. The query bound counts failed, repeated and inactive signing requests.
-/

public section

namespace GXMSS.Interval.Unforgeability

open ENNReal
open OracleComp OracleSpec TweakableHash GXMSS.IntervalMerkle GXMSS.Interval.Filler Encoding
open GXMSS.Reductions GXMSS.Unforgeability GXMSS.Interval.Reductions.Chain
open SyncSignatureUnforgeability

variable {PP T X H M R : Type} {h w v : ℕ}

private theorem combine_separate
    {s a m e f g mr p u vu vp pu pp c n : ℝ≥0∞}
    (hsource : s ≤ a + m + vu + vp + pu + pp)
    (hactive : a ≤ e + f + g + c * p + c * n * u) (hmerkle : m ≤ mr) :
    s ≤ mr + e + f + g + c * p + c * n * u + vu + vp + pu + pp := by
  calc
    s ≤ a + m + vu + vp + pu + pp := hsource
    _ ≤ (e + f + g + c * p + c * n * u) + mr + vu + vp + pu + pp :=
      add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add hactive hmerkle) le_rfl) le_rfl) le_rfl) le_rfl
    _ = _ := by ac_rfl

private theorem chain_coefficients_le_power_of_two
    (I : Interval h) (w v : ℕ) {a p u b c d e : ℝ≥0∞} :
    a + (GXMSS.Interval.activeChainPositionCount I w v : ℝ≥0∞) * p +
        (GXMSS.Interval.activeChainPositionCount I w v : ℝ≥0∞) * ((2 ^ w - 1 : ℕ) : ℝ≥0∞) * u +
        b + c + d + e ≤
      a + ((I.length * v * 2 ^ w : ℕ) : ℝ≥0∞) * p +
        ((I.length * v * (2 ^ w) ^ 2 : ℕ) : ℝ≥0∞) * u + b + c + d + e := by
  have hp : GXMSS.Interval.activeChainPositionCount I w v ≤ I.length * v * 2 ^ w :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hu : GXMSS.Interval.activeChainPositionCount I w v * (2 ^ w - 1) ≤
      I.length * v * (2 ^ w) ^ 2 := by
    calc
      _ ≤ (I.length * v * 2 ^ w) * 2 ^ w := Nat.mul_le_mul hp (Nat.sub_le _ _)
      _ = _ := by ring
  gcongr
  exact_mod_cast hu

/-- The original-domain interval bound has four collision and six separate UD/PRE terms. -/
@[expose] noncomputable def strongUnforgeabilityBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (A : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K I hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction P enc K
            I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A) +
      ((GXMSS.Interval.activeChainPositionCount I w v : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) +
      ((GXMSS.Interval.activeChainPositionCount I w v : ℕ) : ℝ≥0∞) *
        ((2 ^ w - 1 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .endpointVector) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .endpointVector) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .childPair) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .childPair)

/-- Separate original-domain reductions bound every strong interval forgery. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A ≤
      strongUnforgeabilityBound P enc K qs I hv hw A := by
  unfold strongUnforgeabilityBound
  exact combine_separate
    (strongAdvantage_le_merkle_active_and_filler_advantages P enc K I A)
    (activeMatchingMass_le_fixedFallback_advantages P enc K qs I hv hw htwo A hqueries)
    (merkleObstructionMass_le_advantage P enc K I hv A)

/-- Four collision and six separate UD/PRE terms with power-of-two chain coefficients. -/
@[expose] noncomputable def powerOfTwoStrongUnforgeabilityBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (A : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage (merkleTargetCollisionAdversary P enc K I hv A) +
      TargetCollisionResistance.advantage
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction P enc qs K I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction P enc K
            I A) +
      SM_DT_TCR_Advantage
        (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction P enc K I A) +
      ((I.length * v * 2 ^ w : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (chainPreimageReduction P enc K I hv hw A) +
      ((I.length * v * (2 ^ w) ^ 2 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (chainUndetectabilityReduction P enc K I hv hw A) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .endpointVector) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .endpointVector) +
      SM_DT_UD_Advantage (udAdversary P enc K I A .childPair) +
      SM_DT_PRE_Advantage (preAdversary P enc K I A .childPair)

/-- The original-domain theorem also holds with relaxed power-of-two chain coefficients. -/
theorem strong_unforgeability_power_of_two_reduction_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (A : SchemeAdversary PP H M R h v) (hqueries : SigningQueryBound qs A) :
    strongAdvantage (GXMSS.Interval.scheme P enc K I) ProbCompRuntime.probComp A ≤
      powerOfTwoStrongUnforgeabilityBound P enc K qs I hv hw A := by
  apply (strong_unforgeability_reduction_bound P enc K qs I hv hw htwo A hqueries).trans
  unfold strongUnforgeabilityBound powerOfTwoStrongUnforgeabilityBound
  exact chain_coefficients_le_power_of_two I w v

/-- The exact chain-position coefficients are bounded by the power-of-two coefficients. -/
theorem strongUnforgeabilityBound_le_powerOfTwoStrongUnforgeabilityBound
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K qs : ℕ) (I : Interval h)
    (hv : 0 < v) (hw : 0 < w) (A : SchemeAdversary PP H M R h v) :
    strongUnforgeabilityBound P enc K qs I hv hw A ≤
      powerOfTwoStrongUnforgeabilityBound P enc K qs I hv hw A := by
  unfold strongUnforgeabilityBound powerOfTwoStrongUnforgeabilityBound
  exact chain_coefficients_le_power_of_two I w v

end GXMSS.Interval.Unforgeability

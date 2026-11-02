/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.MultiExtractable

/-!
# Public salted Merkle aggregate contracts

An ordinary import exposes the concrete witnesses for every tuple code and varying bounded
depths, together with monotonicity of the scalar error bundle.
-/

public section

open Quantum SaltedMerkle Convexity
open scoped ENNReal

universe v w

open scoped Classical in
example {X Y Msg Salt Z : Type} {k : ℕ} [Fintype X] [DecidableEq X]
    [Fintype Y] [LinearOrder Y] [AddCommGroup Y]
    [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
    [SampleableType Salt] [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i))) Z)
    (dmax : ℕ) (hd : ∀ i, d i ≤ dmax) :
    IsMultiExtractableWith.{v, w} (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (compressedVCOracle k X Y) (multiExtract enc d) code (fun _ ↦ tdBot)
      (StdSimplex.barycenter : StdSimplex ℝ (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).mixedRuntime)
      (merkleErrors (Fintype.card Y) dmax) :=
  SaltedMerkle.isMultiExtractableWith enc d code dmax hd

example (N dmax : ℕ) : (merkleErrors N dmax).Monotone :=
  merkleErrors_monotone N dmax

/-- The total scalar definition also exposes its zero-query boundary. -/
example (N dmax : ℕ) (wVC wME : ℝ≥0∞) :
    (merkleErrors N dmax).offline 0 wVC wME 0 = 0 := by
  simp [merkleErrors, merkleOfflineError]

/-- The bundle retains both bad-database branches before adding the checker term. -/
example (N dmax t : ℕ) (wVC wME : ℝ≥0∞) (qs : ℕ) :
    (merkleErrors N dmax).offline t wVC wME qs =
      min 1 ((2 * min (24 * (t : ℝ≥0∞) * min wVC t * (t - 1 : ℕ))
        ((7 * (t : ℝ≥0∞) + 5) * t * min wVC t / 4) +
        8 * (qs * (dmax + 1) : ℕ)) / N) := rfl

/-- At two queries the collision numerator is `19/2`, below the generic `48`. -/
example : merkleOfflineError 100 0 2 1 0 = 19 / 100 := by
  norm_num [merkleOfflineError]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)) (by finiteness)).mp
  simp (disch := norm_num [ENNReal.div_eq_top, ENNReal.mul_eq_top]) only
    [ENNReal.toReal_min, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- Checked reads add their contribution to the collision-sensitive numerator. -/
example : merkleOfflineError 100 1 2 1 1 = 35 / 100 := by
  norm_num [merkleOfflineError]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)) (by finiteness)).mp
  simp (disch := norm_num [ENNReal.div_eq_top, ENNReal.mul_eq_top]) only
    [ENNReal.toReal_min, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- At one query the zero generic branch remains the tighter bound. -/
example : merkleOfflineError 100 0 1 1 0 = 0 := by
  norm_num [merkleOfflineError]

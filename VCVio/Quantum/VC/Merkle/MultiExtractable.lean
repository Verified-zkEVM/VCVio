/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.Offline

/-!
# Multi-extractability of salted Merkle commitments

The existing salted Merkle scheme and extractor satisfy P1–P5 with the ordinary compressed
oracle and its checked classical reads. The reference is the barycenter of random-oracle
mixed runtimes; no sampling instance for the space of hash functions is required.

These are finite-query statistical bounds for arbitrary tuple codes and depths bounded by
`dmax`. P4 gives the challenger checked reads and a fresh extraction response; its adversary
retains ordinary/extraction access. P1, P2 and P5 include the mixed ordinary/read interface.
The offline scalar bound keeps the minimum of the generic and collision numerators,
with collision leading term `(7/2) · min wVC t · t² / N`, plus the checker contribution.
The aggregate asserts neither efficient extraction nor asymptotic security: runtime bounds,
efficient representations and asymptotic parameter choices are separate obligations.

See Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Definition 7.3 and Theorem 8.3.
-/

public section

open Quantum OracleSpec Convexity
open scoped ENNReal

namespace SaltedMerkle

/-- The aggregate errors increase with the query and mass budgets they use, in the sense of
`MEErrors.Monotone`: the simulation, commutation, offline and online errors are monotone in all
their arguments. The extraction-correctness error is not covered by this monotonicity. -/
theorem merkleErrors_monotone (N dmax : ℕ) : (merkleErrors N dmax).Monotone := by
  refine ⟨fun _ _ _ ↦ le_rfl, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [merkleErrors, comErrorBound, Fintype.card_fin]
    gcongr
  · intro a b hab
    rcases hab with ⟨ht, hw, _, hq⟩
    simp only [merkleErrors, merkleOfflineError]
    gcongr
  · intro a b hab
    rcases hab with ⟨ht, hw, _, _⟩
    simp only [merkleErrors, merkleOnlineError]
    gcongr

universe v w

open scoped Classical in
/-- Concrete witnesses for finite-query multi-extractability, with arbitrary tuple encoding. -/
theorem isMultiExtractableWith
    {X Y Msg Salt Z : Type} {k : ℕ} [Fintype X] [DecidableEq X]
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
      (merkleErrors (Fintype.card Y) dmax) := by
  classical
  let : UniformAnswerMeasure (X →ₒ Y) := UniformAnswerMeasure.ofFiniteNonempty _
  refine { admissible := (conditions enc d).admissible
           sim := simulates_compressedVCOracle
           commute := oraclesCommute_compressedVCOracle
           com := ?_
           extract := ?_
           offline := merkle_offline enc d code dmax hd
           online := ?_ }
  · have he : comErrorBound (Y := Fin (Fintype.card Y)) = comErrorBound (Y := Y) := by
      funext t
      simp only [comErrorBound, Fintype.card_fin]
    change ComBound _ _ _ (comErrorBound (Y := Fin (Fintype.card Y)))
    rw [he]
    exact comBound enc d code
  · have he : extractErrorBound (Y := Fin (Fintype.card Y)) =
        extractErrorBound (Y := Y) := by
      funext L n
      simp only [extractErrorBound, Fintype.card_fin]
    change ExtractionCorrect _ _ _ _ (fun _ _ _ n ↦
      extractErrorBound (Y := Fin (Fintype.card Y)) (2 ^ dmax) n)
    rw [he]
    exact extractionCorrect enc d code (2 ^ dmax)
      (fun i ↦ Nat.pow_le_pow_right (by omega) (hd i))
  · dsimp only [merkleErrors]
    convert merkle_online enc d code using 1

end SaltedMerkle

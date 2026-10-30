/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Concrete P2 for salted Merkle extraction

The compressed oracle commutation error is bounded by
`min (4, 24 * min (1, (2s + 1) / |Y|))`. The constant `24` comes from the concrete
online instability bound. Both ordinary-query and summed checked-read commutation defects
after mixed prefixes obey this bound; `4` caps the squared distance between two isometries.

## References

Chiesa, Di, Hu and Zheng, ePrint 2025/2166: oracle commutativity (Definition 7.3, property 2,
p. 50) and its instability reduction (Lemma 9.2, p. 58), together with Merkle instability
(Lemma 8.8, p. 56). The constant-24/cap-four P2 bound is a strengthened bound proved here;
its formula is not the estimate stated in the paper's Theorem 8.3 (p. 53).
-/

public section

open Quantum OracleSpec
open scoped ENNReal

universe v w

namespace SaltedMerkle

variable {Y : Type} [Fintype Y]

/-- The concrete commutation error `C(s)` for salted Merkle extraction. -/
@[expose]
noncomputable def comErrorBound (s : ℕ) : ℝ≥0∞ :=
  min 4 (24 * min 1 ((2 * s + 1 : ℝ≥0∞) / Fintype.card Y))

variable {X Msg Salt Z : Type} [DecidableEq X] [LinearOrder Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ)
  (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i)) Z)

/-- The instability contribution to P2 is at most `24 min (1, (2s + 1) / |Y|)`. -/
theorem comBoundError_le [Finite X] [UniformAnswerMeasure (X →ₒ Y)] (s : ℕ) :
    comBoundError (multiExtract enc d) s ≤
      24 * min 1 ((2 * s + 1 : ℝ≥0∞) / Fintype.card Y) := by
  unfold comBoundError
  gcongr
  exact iSup_le fun j ↦ iSup_le fun tic ↦ iSup_le fun Ds ↦
    instability_onlineLabel_le enc d tic Ds j s

variable [Fintype X] [AddCommGroup Y]

/-- Concrete P2 for ordinary queries and checked reads after mixed prefixes, capped at four. -/
theorem comBound [UniformAnswerMeasure (X →ₒ Y)] :
    ComBound.{v, w} (compressedVCOracle k X Y) (multiExtract enc d) code
      (comErrorBound (Y := Y)) := by
  have h := (comBound_compressedVCOracle (multiExtract enc d) code).mono
    (comBoundError_le enc d)
  exact (comBound_four _ _ code).min h

/-- The summed checked-read/extraction defect is bounded by the same concrete P2 error,
including when the final read address depends on the retained classical outcome. -/
theorem readComError_le [UniformAnswerMeasure (X →ₒ Y)] (s : ℕ)
    {A Env : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (mixedExtSpec k X Y Y Z) A
      (ReadComOut k Y Z Env) α) (ρ : SubState A) (c : α → Fin k × X)
    (hx : x.IsTotalQueryBound s) :
    readComError (compressedVCOracle k X Y) (multiExtract enc d) code x ρ c ≤
      comErrorBound (Y := Y) s :=
  (comBound enc d code).2 s x ρ c hx

/-- The ordinary oracle ports commute exactly, and both extraction defects obey `C(s)`. -/
theorem oraclesCommute_and_comBound [UniformAnswerMeasure (X →ₒ Y)] :
    OraclesCommute (compressedVCOracle k X Y) ∧
      ComBound.{v, w} (compressedVCOracle k X Y) (multiExtract enc d) code
        (comErrorBound (Y := Y)) :=
  ⟨oraclesCommute_compressedVCOracle, comBound enc d code⟩

end SaltedMerkle

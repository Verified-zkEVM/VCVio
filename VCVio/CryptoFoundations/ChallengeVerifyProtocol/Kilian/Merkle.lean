/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian.Soundness
public import VCVio.CryptoFoundations.VectorCommitment.Merkle

/-!
# Soundness of the Kilian transformation with Merkle trees

The Kilian transformation over an addressed Merkle tree (`MerkleVectorCommitment.merkleVC`) is
sound in the random-oracle model with an explicit error: for every statement outside the language
and every cheating prover whose commitment phase makes at most `qc` oracle queries and whose
response makes at most `qr`, the verifier accepts with probability at most

`ε + multiCheckpointROMErrorNumerator (2L - 1) 1 (L - 1) (qc + qr) / |Y|`

for a PCP with soundness error `ε` and a tree with `L` leaves
(`KilianTransformation_merkle_rom_sound`), and so at most

`ε + ((qc + qr)² + (2L - 1)(qc + qr + L - 1)) / |Y|`

(`KilianTransformation_merkle_rom_sound_quadratic`). The proof composes the generic soundness
theorem `KilianTransformation_rom_sound`, with the Merkle transcript extractor, and the online
extraction bound for Merkle trees, `MerkleVectorCommitment.merkleVC_onlineExtractionError_le`.

The PCP's coin type is countable, so that the coins may be drawn before the commitment phase,
which they are independent of.
-/

public section

open OracleComp OracleSpec BinaryTree InductiveMerkleTree MerkleTreeMultiExtractability
  MerkleVectorCommitment KilianTransformation

open scoped NNReal ENNReal

variable {Stmt Wit Query Address Y : Type} {s : Skeleton}
  [DecidableEq Query] [DecidableEq Y] [Finite Y] [SampleableType Y]
  [UniformAnswerMeasure (Query →ₒ Y)]

/-- **Soundness of the Kilian transformation with Merkle trees in the random-oracle model.** If the
PCP is sound with error `ε`, then for every statement `x` outside the language and every cheating
prover `P` whose commitment phase makes at most `qc` queries and whose response makes at most `qr`,
the Kilian verifier over the Merkle tree accepts with probability at most `ε` plus the
multi-extractability error of one checkpoint of `L` leaves and one batch opening. -/
theorem KilianTransformation_merkle_rom_sound (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    [DecidableEq pcp.Symbol] [Inhabited pcp.Symbol] [Countable pcp.Coins]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (addressKey : SkeletonInternalIndex s → Address) (pos : Fin pcp.length ≃ SkeletonLeafIndex s)
    (enc : pcp.Symbol → Y) (dec : Y → Option pcp.Symbol)
    {ε : ℝ≥0} (hpcp : pcp.soundness rel ε) (x : Stmt) (hx : ¬ ∃ w, rel x w) {St : Type}
    (P : DetVectorCommitment.OnlineAdversary Query Y Y St pcp.Coins
      (PartialVec pcp.length pcp.Symbol × Option (BatchOpening Y s)))
    {qc qr : ℕ} (hc : IsTotalQueryBound P.commit qc)
    (hr : ∀ st coins, IsTotalQueryBound (P.respond st coins) qr) :
    romAcceptance pcp (merkleVC model addressKey pos enc dec) x P ≤
      ε + (multiCheckpointROMErrorNumerator (2 * s.leafCount - 1) 1 (s.leafCount - 1) (qc + qr) :
        ℝ≥0∞) * (Nat.card Y : ℝ≥0∞)⁻¹ := by
  classical
  exact (KilianTransformation_rom_sound pcp rel _ (merkleExtract model addressKey pos dec) hpcp x
    hx P).trans (add_le_add le_rfl
      (merkleVC_onlineExtractionError_le model addressKey pos enc dec pcp.sampleCoins P hc hr))

/-- **Soundness of the Kilian transformation with Merkle trees, quadratic form.** Under the
hypotheses of `KilianTransformation_merkle_rom_sound`, with `q = qc + qr` and `L` leaves, the
Kilian verifier accepts with probability at most `ε + (q² + (2L - 1)(q + L - 1)) / |Y|`. -/
theorem KilianTransformation_merkle_rom_sound_quadratic (pcp : PCP Stmt Wit)
    (rel : Stmt → Wit → Bool)
    [DecidableEq pcp.Symbol] [Inhabited pcp.Symbol] [Countable pcp.Coins]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (addressKey : SkeletonInternalIndex s → Address) (pos : Fin pcp.length ≃ SkeletonLeafIndex s)
    (enc : pcp.Symbol → Y) (dec : Y → Option pcp.Symbol)
    {ε : ℝ≥0} (hpcp : pcp.soundness rel ε) (x : Stmt) (hx : ¬ ∃ w, rel x w) {St : Type}
    (P : DetVectorCommitment.OnlineAdversary Query Y Y St pcp.Coins
      (PartialVec pcp.length pcp.Symbol × Option (BatchOpening Y s)))
    {qc qr : ℕ} (hc : IsTotalQueryBound P.commit qc)
    (hr : ∀ st coins, IsTotalQueryBound (P.respond st coins) qr) :
    romAcceptance pcp (merkleVC model addressKey pos enc dec) x P ≤
      ε + (((qc + qr) * (qc + qr) +
        (2 * s.leafCount - 1) * (qc + qr + (s.leafCount - 1)) : ℕ) : ℝ≥0∞) *
          (Nat.card Y : ℝ≥0∞)⁻¹ := by
  refine (KilianTransformation_merkle_rom_sound pcp rel model addressKey pos enc dec hpcp x hx P
    hc hr).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ zero_le))
  exact_mod_cast multiCheckpointROMErrorNumerator_le_quadratic _ _ _ _

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.BatchExtractability
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Sequential

/-!
# Stateful Merkle Multi-Extractability Game

This module supplies the executable shared-ROM game connecting sequential commitment checkpoints
to dynamically selected pruned batch openings. The terminal adversary returns claims without
acceptance bits; `verifyClaims` computes every bit through the query-parametric addressed batch
verifier. The terminal adversary log is snapshotted before honest verification, keeping terminal
checkpoint evolution and fresh verifier queries as separate proof obligations.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleSpec OracleComp BinaryTree InductiveMerkleTree

variable {Cfg Query Address Y : Type}

/-- One dynamically typed opening claim against a purported commitment checkpoint. Membership of
the checkpoint in the recorded state is checked by the failure predicate, rather than trusted as
part of this adversary-controlled package. -/
structure OpeningClaim (Query : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Configuration tag determining the claim's skeleton and address map. -/
  tag : Cfg
  /-- Claimed commitment checkpoint. -/
  checkpoint : Checkpoint Query Y config tag
  /-- Nonempty intrinsic pruned opening. -/
  opening : BatchOpening Y (config.skeleton tag)

/-- Honest verifier cost for one claim, measured by visited internal nodes. -/
def OpeningClaim.queryCount {config : Configuration Cfg Address}
    (claim : OpeningClaim Query Y config) : ℕ :=
  claim.opening.proof.queryCount

/-- Total honest verifier cost for a list of claims. -/
def claimsQueryCount {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) : ℕ :=
  (claims.map OpeningClaim.queryCount).sum

/-- Verify every claim sequentially through the complete query model and preserve its dependent
configuration tag in the resulting attempts. -/
def verifyClaims [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} :
    List (OpeningClaim Query Y config) →
      OracleComp (Query →ₒ Y)
        (List (AnyOpeningAttempt Cfg Query Address Y config))
  | [] => pure []
  | claim :: claims => do
      let accepted ← MerkleTreeBatchExtractability.verifyOpening model
        (config.addressKey claim.tag) claim.checkpoint.root claim.opening
      let attempts ← verifyClaims model claims
      return ⟨claim.tag, {
        checkpoint := claim.checkpoint
        opening := claim.opening
        accepted }⟩ :: attempts

/-- The honest verifier list is bounded by the sum of the proof-dependent structural counts.
This is the safe full-batch overhead; a later disagreement witness may specialize each
accepted failure to one selected path. -/
theorem verifyClaims_isTotalQueryBound [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config)) :
    IsTotalQueryBound (verifyClaims model claims) (claimsQueryCount claims) := by
  induction claims with
  | nil => trivial
  | cons claim claims ih =>
      simp only [verifyClaims, claimsQueryCount, List.map_cons, List.sum_cons]
      exact isTotalQueryBound_bind
        (n₁ := claim.queryCount) (n₂ := claimsQueryCount claims)
        (MerkleTreeBatchExtractability.verifyOpening_isTotalQueryBound model
          (config.addressKey claim.tag) claim.checkpoint.root claim.opening)
        fun _ => isTotalQueryBound_bind (n₁ := claimsQueryCount claims) (n₂ := 0)
          ih fun _ => trivial

/-- Sequential multi-commitment adversary with a terminal, adaptively chosen list of batch
opening claims. The private commitment state remains abstract. -/
structure Adversary (Cfg : Type) (Query : Type) (Address : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Adaptive sequential commitment strategy. -/
  committer : SequentialCommitter Cfg Query Y
  /-- Produce terminal claims after observing the final private and extractor states. -/
  opening : committer.State → ExtractorState Cfg Query Address Y config →
    OracleComp (Query →ₒ Y) (List (OpeningClaim Query Y config))

/-- Observable result of the stateful game. `terminalSuffix` excludes honest verifier queries. -/
structure Transcript (Cfg : Type) (Query : Type) (Address : Type) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- All immutable commitment checkpoints. -/
  extractorState : ExtractorState Cfg Query Address Y config
  /-- Claims paired with honestly computed acceptance bits. -/
  attempts : List (AnyOpeningAttempt Cfg Query Address Y config)
  /-- Query-log segment produced by the terminal opening adversary. -/
  terminalSuffix : MerkleTreeExtractor.QueryLog Query Y

/-- Oracle syntax of the multi-extractability game before installing random-function semantics. -/
def extractabilityInner [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) := do
  let (privateState, extractorState) ← adversary.committer.runFromEmpty config rounds
  let (claims, terminalSuffix) ← (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyClaims model claims
  return { extractorState, attempts, terminalSuffix }

/-- Shared-cache random-oracle interpretation of the stateful game. All commitments, terminal
opening work, and honest verification use one lazy random function. -/
def extractabilityGame [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (extractabilityInner model config rounds adversary)

/-- Strong three-branch proof event on a game transcript. -/
def StrongFailure [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config) : Prop :=
  Failure model.view transcript.extractorState transcript.attempts transcript.terminalSuffix

/-- Textbook-facing two-branch failure event on a game transcript. -/
def PublicFailure [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config) : Prop :=
  TextbookFailure model.view transcript.extractorState transcript.attempts

/-- The strongest proof event deterministically subsumes the public textbook event. -/
theorem PublicFailure.toStrongFailure [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (transcript : Transcript Cfg Query Address Y config)
    (h : PublicFailure model transcript) : StrongFailure model transcript :=
  TextbookFailure.toFailure model.view transcript.extractorState transcript.attempts
    transcript.terminalSuffix h

/-- Probability of the public textbook event is at most probability of the strongest proof event. -/
theorem prob_publicFailure_le_strongFailure
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    Pr[PublicFailure model | extractabilityGame model config rounds adversary] ≤
      Pr[StrongFailure model | extractabilityGame model config rounds adversary] :=
  _root_.probEvent_mono
    (mx := extractabilityGame model config rounds adversary)
    (fun transcript _ h => PublicFailure.toStrongFailure model transcript h)

/-- Any quantitative theorem for the strongest event immediately yields the same bound for the
weaker textbook event. Downstream corollaries should use this theorem rather than repeat the event
decomposition. -/
theorem publicFailure_bound_of_strongFailure_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) (bound : ENNReal)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤ bound) :
    Pr[PublicFailure model | extractabilityGame model config rounds adversary] ≤ bound :=
  (prob_publicFailure_le_strongFailure model config rounds adversary).trans hstrong

end MerkleTreeMultiExtractability

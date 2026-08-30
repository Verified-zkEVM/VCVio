/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Stateful
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Sequential Merkle commitment phases

This module runs an adaptive sequence of Merkle commitment phases while recording one extractor
checkpoint after every emitted root.  Each phase receives the previous phase's private state, may
make homogeneous oracle queries, and selects its next configuration tag adaptively.

`runCommitments` is itself one `OracleComp`.  Calling `withQueryLog` around each phase records only
that phase's query segment; it does not evaluate the phase or install a fresh oracle.  A later game
can therefore interpret the complete runner through one caching random-oracle implementation and
obtain the shared-ROM semantics required by multi-extractability.

This layer deliberately stops before the terminal opening phase.  The opening verifier determines
what auxiliary state and dependent opening claims it needs, and owns the accepted/rejected bit.
Likewise, no query bound or probability statement is attached to this executable runner.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleSpec OracleComp

variable {Cfg Query Y Address S : Type}

/-- Adaptive commitment strategy used by the multi-extractability experiment. -/
structure SequentialCommitter (Cfg Query Y : Type) where
  /-- Private state threaded between commitment phases. -/
  State : Type
  /-- Initial state before the first commitment. -/
  initialState : State
  /-- Phase `round` emits a configuration tag and claimed root, then returns its next state. -/
  commit : (round : ℕ) → State → OracleComp (Query →ₒ Y) (Cfg × Y × State)

/-- Execute `rounds` commitment phases from an explicit round number, state, and extractor state.

The explicit `firstRound` parameter lets a surrounding game resume a sequence without renumbering
the adversary's phase input. -/
def SequentialCommitter.runCommitments
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} :
    (rounds firstRound : ℕ) → committer.State →
      ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y)
        (committer.State × ExtractorState Cfg Query Address Y config)
  | 0, _, state, extractorState => pure (state, extractorState)
  | rounds + 1, firstRound, state, extractorState => do
      let ((tag, root, nextState), phaseLog) ←
        (committer.commit firstRound state).withQueryLog
      committer.runCommitments rounds (firstRound + 1) nextState
        (extractorState.record tag phaseLog root)

/-- Execute a fixed number of commitments from the committer's initial state and an empty
extractor history. -/
def SequentialCommitter.runFromEmpty
    (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ) :
    OracleComp (Query →ₒ Y)
      (committer.State × ExtractorState Cfg Query Address Y config) :=
  committer.runCommitments rounds 0 committer.initialState ExtractorState.empty

@[simp]
theorem SequentialCommitter.runCommitments_zero
    (committer : SequentialCommitter Cfg Query Y)
    {config : Configuration Cfg Address} (firstRound : ℕ) (state : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    committer.runCommitments 0 firstRound state extractorState =
      pure (state, extractorState) := rfl

/-- The pure state transition used after observing one phase output and its local query log. -/
def ExtractorState.recordCommitmentOutput {config : Configuration Cfg Address}
    (extractorState : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y)
    (output : Cfg × Y × S) : ExtractorState Cfg Query Address Y config :=
  extractorState.record output.1 phaseLog output.2.1

@[simp]
theorem ExtractorState.recordCommitmentOutput_cumulativeLog
    {config : Configuration Cfg Address}
    (extractorState : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y)
    (output : Cfg × Y × S) :
    (extractorState.recordCommitmentOutput phaseLog output).cumulativeLog =
      extractorState.cumulativeLog ++ phaseLog := rfl

end MerkleTreeMultiExtractability

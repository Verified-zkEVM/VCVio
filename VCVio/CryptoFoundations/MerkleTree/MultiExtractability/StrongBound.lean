/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Endgame
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.InitializedBound

/-!
# Strong Multi-Extractability Bound

This module connects the generic sequential stopping theorem to the executable stateful game.
The sole remaining semantic interface is `TerminalStrongBound`: after all commitment checkpoints
have been recorded, it bounds terminal opening production plus honest batch verification under
the exact cache/log/stability invariants maintained by the online proof.

The finite-maximum theorem owns the security statement.  The textbook event, coarse binomial
bound, and quadratic bound are corollaries.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MerkleTreeMultiExtractability

variable {Cfg Query Address Y : Type}

/-- Terminal opening production, honest verification, and transcript assembly. -/
def Adversary.terminalExecution [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (privateState : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) (Transcript Cfg Query Address Y config) := do
  let (claims, terminalSuffix) ←
    (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyClaims model claims
  return { extractorState, attempts, terminalSuffix }

/-- The executable inner game is the initialized sequential runner followed by
`terminalExecution`. -/
theorem extractabilityInner_eq_runFromEmptyThen [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config) :
    extractabilityInner model config rounds adversary =
      adversary.committer.runFromEmptyThen config rounds
        (adversary.terminalExecution model) := rfl

/-- Pointwise terminal theorem required by sequential composition.  This named interface makes
the last cryptographic obligation auditable: no checkpoint evolution or query accounting is
hidden inside it. -/
def Adversary.TerminalStrongBound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead terminalQueryBound : ℕ) : Prop :=
  ∀ privateState (state : ExtractorState Cfg Query Address Y config)
      (terminalCached : ℕ) (cache : (Query →ₒ Y).QueryCache)
      (log : (Query →ₒ Y).QueryLog),
    state.cumulativeLog = log →
    ¬ CacheHasCollision cache →
    (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
      ∀ input, cache input ≠ none → input ∈ keys) →
    (∀ entry ∈ log, cache entry.1 = some entry.2) →
    (∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
    state.StableAt model.view log →
    Pr[ fun z => StrongFailure model z.1 |
      (simulateQ (Query →ₒ Y).cachingOracle
        (adversary.terminalExecution model privateState state)).run cache] ≤
      (multiExtractabilitySafePotential nodeBudget checkpointCount verifierOverhead
        terminalQueryBound terminalCached : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹

/-- **Strongest game-level finite-maximum theorem.**

The adversary may choose configuration tags, roots, and terminal batch selectors adaptively.
Every phase shares one cached homogeneous random oracle.  The hypotheses expose exactly the
uniform structural resources required for a finite public bound. -/
theorem strongFailure_rom_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
      perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hterminal : adversary.TerminalStrongBound model nodeBudget checkpointCount
      verifierOverhead terminalQueryBound) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  have hraw := adversary.committer.probEvent_runFromEmptyThen_le model.view config
    (adversary.terminalExecution model) (StrongFailure model) paddingQuery
    phaseQueryBound terminalQueryBound nodeBudget checkpointCount verifierOverhead
    hcommit perCheckpoint hconfig hterminal rounds hnodes hcheckpoints
  rw [extractabilityGame, OracleSpec.withCacheOverlay, StateT.run'_eq,
    extractabilityInner_eq_runFromEmptyThen, probEvent_map]
  simpa [Function.comp_def] using hraw

/-- Exact uniform-shape specialization of the strongest game-level theorem. -/
theorem strongFailure_rom_bound_exact
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (paddingQuery : Query)
    (phaseQueryBound terminalQueryBound verifierOverhead perCheckpoint : ℕ)
    (hcommit : ∀ round privateState,
      IsTotalQueryBound (adversary.committer.commit round privateState) phaseQueryBound)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hterminal : adversary.TerminalStrongBound model (rounds * perCheckpoint) rounds
      verifierOverhead terminalQueryBound) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator (rounds * perCheckpoint) rounds verifierOverhead
        (rounds * phaseQueryBound + terminalQueryBound) : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ :=
  strongFailure_rom_bound model config rounds adversary paddingQuery phaseQueryBound
    terminalQueryBound (rounds * perCheckpoint) rounds verifierOverhead perCheckpoint
    hcommit hconfig le_rfl le_rfl hterminal

/-- The public textbook failure event inherits the strongest finite-maximum bound. -/
theorem publicFailure_rom_bound
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ PublicFailure model | extractabilityGame model config rounds adversary] ≤
      (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  publicFailure_bound_of_strongFailure_bound model config rounds adversary _ hstrong

/-- Coarse binomial corollary of the strongest finite-maximum bound. -/
theorem strongFailure_rom_bound_coarse
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_coarse nodeBudget checkpointCount
    verifierOverhead queryBound

/-- Quadratic corollary of the strongest finite-maximum bound. -/
theorem strongFailure_rom_bound_quadratic
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary Cfg Query Address Y config)
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ)
    (hstrong :
      Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
        (multiExtractabilitySafeNumerator nodeBudget checkpointCount verifierOverhead
          queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹) :
    Pr[ StrongFailure model | extractabilityGame model config rounds adversary] ≤
      ((queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) : ℕ) : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine hstrong.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast multiExtractabilitySafeNumerator_le_quadratic nodeBudget checkpointCount
    verifierOverhead queryBound

end MerkleTreeMultiExtractability

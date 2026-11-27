/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.FilteredView
public import HashSigTest.GXMSS.SplicedView
import all HashSig.GXMSS.Security.Interval.Reductions.FilteredView
import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSigTest.GXMSS.SplicedView

/-!
# Returned failures and absorbing filtered splice controls

A first successful word below the selected cut kills the option state. Subsequent signing
requests skip retry randomness; returned inactive failure instead retains a consumed history.
The good adaptive view preserves both retry draws and the complete returned result.
-/

public section
namespace GXMSS.FilteredViewProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Reductions GXMSS.Reductions GXMSS.SplicedViewProbe
open SyncSignatureUnforgeability IncomparableEncoding OracleComp OracleSpec

/-- Successful true messages emit a word strictly below the selected positive cut. -/
@[expose] def lowEncoding : IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 where
  code := {fun _ => 0}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm)).elim
  encode := fun _ msg _ _ => if msg then some ⟨fun _ => 0, Set.mem_singleton _⟩ else none

/-- Returned inactive failure consumes the original request while keeping a live history. -/
private theorem inactive_is_returned :
    contextFilteredSplicedSigningOracle hash enc 1 (intervalChainContext hash middle fillers)
      () guess guess false starts (splicedEndpoints hash () guess false starts)
      (2, false) (some emptyHistory) =
      pure (none, some (Function.update emptyHistory 2 (some (false, none)))) := by
  rfl

/-- An already killed state stays killed without a signing randomizer draw. -/
private theorem killed_is_absorbing (ep : Fin 8) (msg : Bool) :
    contextFilteredSplicedSigningOracle hash enc 1 (intervalChainContext hash middle fillers)
      () guess guess false starts (splicedEndpoints hash () guess false starts)
      (ep, msg) none = pure (none, none) := rfl

/-- The first active success kills the full view after its one retry draw. -/
theorem killed_adaptive_program (response : Bool) :
    filteredChainSpliceView hash lowEncoding 1 middle adversary () guess guess response
      starts fillers = (do
        let _ ← ($ᵗ Unit : ProbComp Unit)
        pure none) := by
  cases response <;>
    dsimp only [filteredChainSpliceView, runContextFilteredSpliced, adversary, signingQuery,
      Forgery, ExperimentResult] <;>
    simp only [map_bind, run_simulateQ_query_bind, simulateQ_pure,
      StateT.run_pure, QueryImpl.add_apply_inr] <;>
    dsimp only [StateT.run, StateT.bind, StateT.pure,
      contextFilteredSplicedSigningOracle, intervalChainContext] <;>
    simp [IncomparableEncoding.retry_one, IncomparableEncoding.attempt, lowEncoding,
      IncomparableEncoding.value, emptyHistory, Function.update, Epoch.IsActive,
      middle, guess, guessedEpoch, guessedChain, guessedPosition,
      map_eq_bind_pure_comp, bind_assoc]

/-- A good selected word preserves both draws, complete output and first-message history. -/
theorem good_adaptive_program (response : Bool) :
    filteredChainSpliceView hash enc 1 middle adversary () guess guess response starts fillers =
      (do
        let _ ← ($ᵗ Unit : ProbComp Unit)
        let _ ← ($ᵗ Unit : ProbComp Unit)
        pure (some (expected response))) := by
  cases response <;>
    dsimp only [filteredChainSpliceView, runContextFilteredSpliced, adversary, signingQuery,
      Forgery, ExperimentResult] <;>
    simp only [map_bind, run_simulateQ_query_bind, simulateQ_pure,
      StateT.run_pure, QueryImpl.add_apply_inr] <;>
    dsimp only [StateT.run, StateT.bind, StateT.pure,
      contextFilteredSplicedSigningOracle, intervalChainContext] <;>
    simp [IncomparableEncoding.retry_one, IncomparableEncoding.attempt, enc,
      IncomparableEncoding.value, emptyHistory, Function.update, Epoch.IsActive,
      middle, guess, signature, intervalSplicedSignatureOfWord,
      contextSplicedSignatureOfWord, splicedChainValue, guessedEpoch, guessedChain,
      guessedPosition, expected, expectedHistory, map_eq_bind_pure_comp, bind_assoc] <;>
    rfl

end GXMSS.FilteredViewProbe

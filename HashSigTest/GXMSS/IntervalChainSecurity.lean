/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.Experiments
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
public import HashSig.GXMSS.Security.Reductions.Interval.Chain
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation

/-!
# Interval chain security controls

The closed controls reduce the filtered signing handlers to explicit live and absorbing
programs, retaining their Unit retry draws. They pin the non-honest OTS bit and the live
failed-consumed history. A returned OTS response selects an unused inactive epoch. The
  original-domain chain
bounds are consumed through their actual named strategies and proofs.

Private imports supply the actual implementation kernels used by these controls. Ordinary public
endpoint applications live in `DirectEndpointApplications`.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Reductions
open GXMSS.Reductions SyncSignatureUnforgeability
open OracleComp OracleSpec

#check @GXMSS.Interval.Reductions.Chain.encodingCollisionMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainCollisionMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.chainCutCollisionMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.selectedPreimageMass_le_advantage
#check @GXMSS.Interval.Reductions.Chain.selectedSource_native_telescope

-- Closed controls use local fixture bindings, so the probe adds no public API.
#check
  let middle : Interval 3 := ⟨3, 4, by decide⟩
  let P : HashInstance Unit ((Fin 8 × Fin 1 × Fin 3) ⊕ (Fin 4 × Fin 8))
      (Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))) Bool 3 2 1 := {
    thf := ⟨pure (), fun _ _ input => match input with | .inl x => !x | .inr _ => false⟩
    digestInput := ⟨Sum.inl, Sum.inl_injective⟩
    pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
      Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
    vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
      Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
    chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
    treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
    chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t) }
  let enc (digit : Fin 4) : Encoding.IncomparableEncoding Unit Bool Unit (Fin 8) 1 4 := {
    code := {fun _ => digit}
    incomparable := singletonCode_incomparable (fun _ => digit)
    encode := fun _ message _ _ =>
      if message then some ⟨(fun _ => digit), Set.mem_singleton _⟩ else none }
  let query (epoch : Fin 8) (message : Bool) :
      OracleComp (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1))
        (Option (GXMSS.Signature Unit Bool 3 1)) :=
    (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1)).query
      (.inr (epoch, message))
  let A : SchemeAdversary Unit Bool Bool Unit 3 1 := { forge := fun _ => do
    let _ ← query 0 false
    let _ ← query 0 true
    let answer ← query 3 true
    let _ ← query 3 false
    let _ ← query 4 false
    let _ ← query 4 true
    match answer with
    | none => return (3, true, ⟨(), fun _ => false, fun _ => false⟩)
    | some signature =>
      let _ ← query (if signature.ots 0 then 1 else 6) true
      return (3, true, signature) }
  let starts : Fin 8 → Fin 1 → Bool := fun _ _ => false
  let fillers : Fillers middle Bool := fun _ => false
  let selector : Guess 3 2 1 := (3, 0, ⟨2, by decide⟩)
  let splice : Guess 3 2 1 := (3, 0, ⟨0, by decide⟩)
  let endpoints := splicedEndpoints P () splice false starts
  let signature := intervalSplicedSignatureOfWord P middle () splice false starts
    endpoints fillers 3 ((fun _ => (3 : Fin 4)), ())
  let expectedHistory : History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) :=
    let h₀ := Function.update emptyHistory 0 (some (false, none))
    let h₁ := Function.update h₀ 3 (some (true, some signature))
    let h₂ := Function.update h₁ 4 (some (false, none))
    Function.update h₂ 6 (some (true, none))
  let expected : ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) :=
    (⟨GXMSS.IntervalMerkle.root P middle () endpoints fillers, ()⟩,
      (3, true, signature), expectedHistory)
  (show
    (filteredChainSpliceView P (enc 3) 1 middle A () selector splice false starts fillers = do
      let _ ← ($ᵗ Unit : ProbComp Unit)
      let _ ← ($ᵗ Unit : ProbComp Unit)
      pure (some expected)) ∧
    (filteredChainSpliceView P (enc 1) 1 middle A () selector splice false starts fillers = do
      let _ ← ($ᵗ Unit : ProbComp Unit)
      pure none) ∧
    signature.ots 0 = false ∧
    signature.ots 0 ≠ P.chain () 3 0 0 3 (starts 3 0) ∧
    false ≠ P.chain () 3 0 0 1 (starts 3 0) ∧
    expectedHistory 4 = some (false, none) ∧
    expectedHistory 6 = some (true, none) from by
      have hots : signature.ots 0 = false := by
        simp [signature, endpoints, intervalSplicedSignatureOfWord, splicedChainValue,
          splice, P, starts, guessedEpoch, guessedChain, guessedPosition,
          HashInstance.chain_succ, HashInstance.chain_zero]
      refine ⟨?_, ?_, hots, ?_, ?_, ?_, ?_⟩
      · dsimp only [filteredChainSpliceView, runContextFilteredSpliced, A, query,
          Forgery, ExperimentResult]
        simp only [run_simulateQ_query_bind,
          QueryImpl.add_apply_inr]
        dsimp only [StateT.run, StateT.bind, StateT.pure, contextFilteredSplicedSigningOracle]
        simp [enc, Encoding.IncomparableEncoding.retry, Encoding.IncomparableEncoding.value,
          intervalChainContext, Epoch.IsActive, middle, selector, splice, signature,
          contextSplicedSignatureOfWord, intervalSplicedSignatureOfWord,
          splicedChainValue, guessedEpoch, guessedChain, guessedPosition,
          expected, expectedHistory, endpoints, emptyHistory, Function.update, P, starts,
          map_eq_bind_pure_comp, bind_assoc, HashInstance.chain_succ, HashInstance.chain_zero]
        rfl
      · dsimp only [filteredChainSpliceView, runContextFilteredSpliced, A, query,
          Forgery, ExperimentResult]
        simp only [run_simulateQ_query_bind,
          QueryImpl.add_apply_inr]
        dsimp only [StateT.run, StateT.bind, StateT.pure, contextFilteredSplicedSigningOracle]
        simp [enc, Encoding.IncomparableEncoding.retry, Encoding.IncomparableEncoding.value,
          intervalChainContext, Epoch.IsActive, middle, selector, emptyHistory, Function.update,
          guessedEpoch, guessedChain, guessedPosition, map_eq_bind_pure_comp, bind_assoc]
        rfl
      · rw [hots]
        simp [P, starts, HashInstance.chain_succ, HashInstance.chain_zero]
      · simp [P, starts, HashInstance.chain_succ, HashInstance.chain_zero]
      · simp [expectedHistory]
      · simp [expectedHistory])

namespace IntervalFrontierControls

/-- A height-three singleton has three maximal inactive subtree roots. -/
theorem singleton_frontier_card :
    Fintype.card (Subtree.FrontierNode (⟨3, 3, by decide⟩ : Interval 3)) = 3 := by decide

private def singleton3 : Interval 3 := ⟨3, 3, by decide⟩

private inductive BoolInput (v : ℕ) where
  | digest : Bool → BoolInput v
  | pair : Bool × Bool → BoolInput v
  | vector : (Fin v → Bool) → BoolInput v

private inductive BoolTweak (h w v : ℕ) where
  | chain : Fin (2 ^ h) × Fin v × Fin (2 ^ w - 1) → BoolTweak h w v
  | tree : Fin (h + 1) × Fin (2 ^ h) → BoolTweak h w v

private def constantBoolHash (h w v : ℕ) :
    GXMSS.HashInstance Unit (BoolTweak h w v) (BoolInput v) Bool h w v where
  thf := ⟨pure (), fun _ _ _ => false⟩
  digestInput := ⟨BoolInput.digest, by intro a b hab; cases hab; rfl⟩
  pairInput := ⟨BoolInput.pair, by intro a b hab; cases hab; rfl⟩
  vectorInput := ⟨BoolInput.vector, by intro a b hab; cases hab; rfl⟩
  chainTweak := ⟨BoolTweak.chain, by intro a b hab; cases hab; rfl⟩
  treeTweak := ⟨BoolTweak.tree, by intro a b hab; cases hab; rfl⟩
  chain_ne_tree := by intro c t h; cases h

private def boolP := constantBoolHash 3 1 1

private def boolXs : Fin 8 → Fin 1 → Bool := fun _ _ => false

private def boolYs : Fin 1 → Bool := fun _ => false

private def boolAuth : Fin 3 → Bool := fun _ => false

/-- The singleton's adjacent inactive leaf exposes a vector preimage. -/
example : GXMSS.Interval.MerkleWitnesses.extractInactiveOpening boolP singleton3
    () boolXs (fun _ => false) 2 (by decide) boolYs boolAuth =
      .inl (.inl boolYs) := by decide

/-- An inactive block of two leaves exposes an ordered pair preimage. -/
example : GXMSS.Interval.MerkleWitnesses.extractInactiveOpening boolP singleton3
    () boolXs (fun _ => false) 0 (by decide) boolYs boolAuth =
      .inl (.inr (false, false)) := by decide

/-- A different sampled filler makes the finite finder return the honest-first
ordered pair at the original root address. -/
example : GXMSS.Interval.MerkleWitnesses.findAboveFrontier boolP singleton3
    () boolXs (fun _ => true) 0 boolYs boolAuth =
      some (2, (false, true), (false, false)) := by decide

/-- The singleton's reachable pair targets are its three active-leaf ancestors. -/
example : (GXMSS.Interval.MerkleWitnesses.honestTargetQueries boolP singleton3
    () boolXs (fun _ => false)).length = 3 := by decide

private def interval24 : Interval 3 := ⟨2, 4, by decide⟩

/-- The isolated inactive leaf at epoch five opens the vector domain. -/
example : GXMSS.Interval.MerkleWitnesses.extractInactiveOpening boolP interval24
    () boolXs (fun _ => false) 5 (by decide) boolYs boolAuth =
      .inl (.inl boolYs) := by decide

/-- The inactive left block opens an ordered child-pair domain. -/
example : GXMSS.Interval.MerkleWitnesses.extractInactiveOpening boolP interval24
    () boolXs (fun _ => false) 0 (by decide) boolYs boolAuth =
      .inl (.inr (false, false)) := by decide

/-- Above the left frontier, the honest pair keeps the sampled filler in its left slot. -/
example : GXMSS.Interval.MerkleWitnesses.findAboveFrontier boolP interval24
    () boolXs (fun _ => true) 0 boolYs boolAuth =
      some (1, (true, false), (false, false)) := by decide

/-- Above the right frontier, the honest pair keeps the sampled filler in its right slot. -/
example : GXMSS.Interval.MerkleWitnesses.findAboveFrontier boolP interval24
    () boolXs (fun _ => true) 6 boolYs boolAuth =
      some (1, (false, true), (false, false)) := by decide

end IntervalFrontierControls

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Reductions.Interval.ActiveSimulation

/-!
# Adaptive active interval splice controls

The local fixture observes inactive failure/repetition, active success/repetition, active retry
exhaustion/repetition, and an additional request whose epoch depends on a returned OTS response.
Both actual replacement views equal two explicit retry draws followed by the expected whole
result, including their first-message history. Generic controls also pin the selected positive
OTS digit and terminal endpoint to a non-honest response.

Private imports supply the actual implementation kernels used by these controls. Ordinary public
endpoint applications live in `DirectEndpointApplications`.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Reductions
open GXMSS.Reductions SyncSignatureUnforgeability
open OracleComp OracleSpec

#check @chainSpliceView_honest
#check @GXMSS.Interval.Reductions.encodingTargetCollisionReduction

#check
  let middle : Interval 3 := ⟨3, 4, of_decide_eq_true rfl⟩
  let P : HashInstance Unit ((Fin 8 × Fin 1 × Fin 1) ⊕ (Fin 4 × Fin 8))
      (Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))) Bool 3 1 1 := {
    thf := ⟨pure (), fun _ _ _ => false⟩
    digestInput := ⟨Sum.inl, Sum.inl_injective⟩
    pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
      Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
    vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
      Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
    chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
    treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
    chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t) }
  let enc : Encoding.IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 := {
    code := {fun _ => 1}
    incomparable := singletonCode_incomparable (fun _ => 1)
    encode := fun _ msg _ _ => if msg then some ⟨(fun _ => 1), Set.mem_singleton _⟩ else none }
  let starts : Fin 8 → Fin 1 → Bool := fun _ _ => false
  let fillers : Fillers middle Bool := fun _ => false
  let guess : Guess 3 1 1 := (3, 0, ⟨0, of_decide_eq_true rfl⟩)
  let signature : Bool → GXMSS.Signature Unit Bool 3 1 := fun response =>
    intervalSplicedSignatureOfWord P middle () guess response starts
      (splicedEndpoints P () guess response starts) fillers 3 ((fun _ => 1), ())
  let query (ep : Fin 8) (msg : Bool) :
      OracleComp (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1))
        (Option (GXMSS.Signature Unit Bool 3 1)) :=
    (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1)).query (.inr (ep, msg))
  let A : Adversary unifSpec (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) := { forge := fun _ => do
    let inactive ← query 2 false
    let inactiveRepeat ← query 2 true
    let success ← query 3 true
    let successRepeat ← query 3 false
    let exhausted ← query 4 false
    let exhaustedRepeat ← query 4 true
    let response := (success.map fun sig => sig.ots 0).getD false
    let extra ← query (if response then 1 else 6) true
    let checks := inactive.isNone && inactiveRepeat.isNone && success.isSome &&
      successRepeat.isNone && exhausted.isNone && exhaustedRepeat.isNone && extra.isNone
    pure (3, checks && response, success.getD (signature false)) }
  let expectedHistory (response : Bool) : History (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) :=
    let h₁ := Function.update emptyHistory 2 (some (false, none))
    let h₂ := Function.update h₁ 3 (some (true, some (signature response)))
    let h₃ := Function.update h₂ 4 (some (false, none))
    Function.update h₃ (if response then 1 else 6) (some (true, none))
  let expected (response : Bool) : ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8)
      Bool (GXMSS.Signature Unit Bool 3 1) :=
    (⟨GXMSS.IntervalMerkle.root P middle ()
      (splicedEndpoints P () guess response starts) fillers, ()⟩,
      (3, response, signature response), expectedHistory response)
  (show ∀ response : Bool,
    chainSpliceView P enc 1 middle A () guess response starts fillers = (do
      let _ ← ($ᵗ Unit : ProbComp Unit)
      let _ ← ($ᵗ Unit : ProbComp Unit)
      pure (expected response)) from by
    intro response
    cases response <;>
      dsimp only [chainSpliceView, A, query, Forgery, ExperimentResult] <;>
      simp only [run_simulateQ_query_bind, simulateQ_pure, StateT.run_pure,
        QueryImpl.add_apply_inr] <;>
      dsimp only [StateT.run, StateT.bind, StateT.pure, intervalSplicedSigningOracle] <;>
      simp [enc, Encoding.IncomparableEncoding.retry, Encoding.IncomparableEncoding.value,
        Epoch.IsActive, middle, guess, signature, intervalSplicedSignatureOfWord,
        splicedChainValue, guessedEpoch, guessedChain, guessedPosition,
        expected, expectedHistory, map_eq_bind_pure_comp, bind_assoc] <;>
      rfl)

#check @filteredChainSpliceView_advance

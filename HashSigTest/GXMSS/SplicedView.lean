/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import all HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Chain

/-!
# Full adaptive interval splice controls

The two concrete replacement responses change the successful OTS value and an adaptive request.
The exact program retains two retry draws, returned failures, repetitions and first messages.
Private imports expose only the implementation kernels used in these concrete controls.
-/

public section
namespace GXMSS.SplicedViewProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Reductions GXMSS.Reductions
open SyncSignatureUnforgeability IncomparableEncoding OracleComp OracleSpec

/-- Two interior active epochs leave both adaptive extra requests inactive. -/
@[expose] def middle : Interval 3 := ⟨3, 4, by decide⟩

/-- Tagged raw domains with a constant hash expose the replacement response directly. -/
@[expose] def hash : HashInstance Unit ((Fin 8 × Fin 1 × Fin 1) ⊕ (Fin 4 × Fin 8))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))) Bool 3 1 1 where
  thf := ⟨pure (), fun _ _ _ => false⟩
  digestInput := ⟨Sum.inl, Sum.inl_injective⟩
  pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
    Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
  vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
    Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
  chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
  treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
  chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t)

/-- A true message returns the maximum singleton word; a false message exhausts. -/
@[expose] def enc : IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 where
  code := {fun _ => 1}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans
      (Set.mem_singleton_iff.mp hy).symm)).elim
  encode := fun _ msg _ _ => if msg then some ⟨fun _ => 1, Set.mem_singleton _⟩ else none

/-- Every original chain starts with false. -/
@[expose] def starts : Fin 8 → Fin 1 → Bool := fun _ _ => false

/-- Retained inactive frontier values are false. -/
@[expose] def fillers : Fillers middle Bool := fun _ => false

/-- The only positive position of the selected epoch's only chain. -/
@[expose] def guess : Guess 3 1 1 := (3, 0, ⟨0, by decide⟩)

/-- The complete successful payload has the supplied response and its actual mixed-tree path. -/
def signature (response : Bool) : GXMSS.Signature Unit Bool 3 1 :=
  intervalSplicedSignatureOfWord hash middle () guess response starts
    (splicedEndpoints hash () guess response starts) fillers 3 ((fun _ => 1), ())

private def signingQuery (ep : Fin 8) (msg : Bool) :
    OracleComp (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1))
      (Option (GXMSS.Signature Unit Bool 3 1)) :=
  (unifSpec + signingSpec (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1)).query (.inr (ep, msg))

/-- The final extra request depends on the actual returned OTS response. -/
def adversary : SchemeAdversary Unit Bool Bool Unit 3 1 where
  forge _ := do
    let inactive ← signingQuery 2 false
    let inactiveRepeat ← signingQuery 2 true
    let success ← signingQuery 3 true
    let successRepeat ← signingQuery 3 false
    let exhausted ← signingQuery 4 false
    let exhaustedRepeat ← signingQuery 4 true
    let response := (success.map fun sig => sig.ots 0).getD false
    let extra ← signingQuery (if response then 1 else 6) true
    let checks := inactive.isNone && inactiveRepeat.isNone && success.isSome &&
      successRepeat.isNone && exhausted.isNone && exhaustedRepeat.isNone && extra.isNone
    pure (3, checks && response, success.getD (signature false))

/-- First-request history preserves the original inactive, successful and exhausted messages. -/
@[expose] def expectedHistory (response : Bool) :
    History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) :=
  let h₁ := Function.update emptyHistory 2 (some (false, none))
  let h₂ := Function.update h₁ 3 (some (true, some (signature response)))
  let h₃ := Function.update h₂ 4 (some (false, none))
  Function.update h₃ (if response then 1 else 6) (some (true, none))

/-- The complete returned observation includes the actual mixed-tree public root. -/
def expected (response : Bool) :
    ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) :=
  (⟨root hash middle () (splicedEndpoints hash () guess response starts) fillers, ()⟩,
    (3, response, signature response), expectedHistory response)

/-- Exactly the two fresh active requests draw retry randomness. -/
theorem whole_adaptive_program (response : Bool) :
    chainSpliceView hash enc 1 middle adversary () guess response starts fillers = (do
      let _ ← ($ᵗ Unit : ProbComp Unit)
      let _ ← ($ᵗ Unit : ProbComp Unit)
      pure (expected response)) := by
  cases response <;>
    dsimp only [chainSpliceView, adversary, signingQuery, Forgery, ExperimentResult,
      runWithSigningKernel, oraclesWithSigningKernel] <;>
    simp only [run_simulateQ_query_bind, simulateQ_pure, StateT.run_pure,
      QueryImpl.add_apply_inr] <;>
    dsimp only [StateT.run, StateT.bind, StateT.pure, signingKernelOracle,
      intervalSplicedSign, contextSplicedSign, intervalChainContext] <;>
    simp [IncomparableEncoding.retry_one, IncomparableEncoding.attempt, enc,
      IncomparableEncoding.value, record, emptyHistory, Function.update,
      Epoch.IsActive, middle, guess, signature, intervalSplicedSignatureOfWord,
      contextSplicedSignatureOfWord, splicedChainValue, guessedEpoch, guessedChain,
      guessedPosition, expected, expectedHistory, map_eq_bind_pure_comp, bind_assoc] <;>
    rfl

/-- Honest responses recover the actual ordinary interval view for every adversary. -/
theorem honest_view (A : SchemeAdversary Unit Bool Bool Unit 3 1) :
    chainSpliceView hash enc 1 middle A () guess false starts fillers =
      GXMSS.Interval.viewFromKeys hash enc 1 middle A () starts fillers :=
  chainSpliceView_honest hash enc 1 middle A () guess starts fillers

end GXMSS.SplicedViewProbe

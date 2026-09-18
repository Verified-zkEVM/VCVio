/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Execution
public import VCVioTest.InnerProduct.Comparison

/-!
# Ordinary-import consumers of the inner-product execution comparison

Compose the complete execution comparison with the independent plain-effect evaluator.
-/

public section

open Interaction Interaction.TwoParty InnerProduct

namespace InnerProductExecutionTest

variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]

/-- The independent plain-effect evaluator retains the same complete observation. -/
theorem plain_execution_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (sample : m Fˣ) {r : Nat} (s : Statement F G r) (p : Prover F G r)
    (observe : ((_tr : PFunctor.FreeM.Path (protocolTree F G r)) × Unit × Bool) → A) :
    observe <$> TwoParty.run (protocolTree F G r) (protocolRoles F G r)
      (proverStrategy (m := m) p) (PublicCoinCounterpart.toCounterpart (publicVerifier sample s)) =
      PlainReplay.run (fun _ => sample)
        (InnerProduct.Plain.source p (fun tr => observe ⟨transcriptPath tr, (), accepts s tr⟩)) :=
  (InnerProduct.Execution.run_observe sample s p observe).trans
    (InnerProduct.Comparison.run_eq p _ sample)

/-- A challenge handler that observes and advances a private counter. -/
@[expose]
def countingChallenge (choose : ℕ → Fˣ) : StateT ℕ Id Fˣ :=
  fun state => (choose state, state + 1)

example (choose : ℕ → Fˣ) (s : Statement F G 0) (p : Prover F G 0) (state : ℕ) :
    (TwoParty.run (protocolTree F G 0) (protocolRoles F G 0)
      (proverStrategy (m := StateT ℕ Id) p)
      (PublicCoinCounterpart.toCounterpart (publicVerifier (countingChallenge choose) s))).run
        state = (⟨transcriptPath (.terminal p), (), accepts s (.terminal p)⟩, state) := by
  rw [InnerProduct.Execution.execution_state_eq]
  rfl

example (choose : ℕ → Fˣ) (s : Statement F G 1) (msg : FoldMessage F G)
    (next : Fˣ → Prover F G 0) (state : ℕ) :
    (TwoParty.run (protocolTree F G 1) (protocolRoles F G 1)
      (proverStrategy (m := StateT ℕ Id) (msg, next))
      (PublicCoinCounterpart.toCounterpart (publicVerifier (countingChallenge choose) s))).run
        state =
      (⟨transcriptPath (.step msg (choose state) (.terminal (next (choose state)))), (),
        accepts s (.step msg (choose state) (.terminal (next (choose state))))⟩, state + 1) := by
  exact (InnerProduct.Execution.execution_state_eq (countingChallenge choose) s
    (msg, next) state).trans rfl

end InnerProductExecutionTest

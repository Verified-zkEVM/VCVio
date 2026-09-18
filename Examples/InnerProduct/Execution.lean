/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Interaction

/-!
# Complete inner-product protocol executions

The two-party interaction and the oracle source program retain the same full transcript path
and both party outputs. The comparison is valid for any lawful monad, including a stateful
challenge handler whose final private state remains part of the result.
-/

public section

open Interaction Interaction.TwoParty
open InnerProduct

namespace InnerProduct.Execution

-- Keep dependent path types aligned when rewriting the public execution equations.
attribute [local implicit_reducible] protocolTree protocolRoles Prover

variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]

/-- Every observation of the complete interaction agrees with the source program. -/
theorem run_observe {m : Type → Type} [Monad m] [LawfulMonad m]
    (sample : m Fˣ) {r : Nat} (s : Statement F G r) (p : Prover F G r)
    (observe : ((_tr : PFunctor.FreeM.Path (protocolTree F G r)) × Unit × Bool) → A) :
    observe <$> TwoParty.run (protocolTree F G r) (protocolRoles F G r)
      (proverStrategy (m := m) p) (PublicCoinCounterpart.toCounterpart (publicVerifier sample s)) =
      simulateQ (fun _ => sample)
        (source p (fun tr => observe ⟨transcriptPath tr, (), accepts s tr⟩)) := by
  induction r generalizing A with
  | zero =>
      simp only [proverStrategy, publicVerifier, protocolTree, protocolRoles,
        PublicCoinCounterpart.toCounterpart_sender,
        source, transcriptPath]
      have h := TwoParty.run_sender (m := m) (rest := fun (_ : Witness F 0) => .done)
        (rRest := fun _ => PUnit.unit) (OutputP := fun _ => Unit) (OutputC := fun _ => Bool)
        (pure ⟨p, ()⟩) (fun w => PublicCoinCounterpart.toCounterpart <$>
          pure (accepts s (.terminal w)))
      exact (congrArg (fun out => observe <$> out) h).trans (by
        simp only [pure_bind, map_pure, PublicCoinCounterpart.toCounterpart_done,
          TwoParty.run_done]
        erw [map_pure, simulateQ_pure]
        rfl)
  | succ r ih =>
      obtain ⟨msg, next⟩ := p
      simp only [proverStrategy, publicVerifier, protocolTree, protocolRoles,
        PublicCoinCounterpart.toCounterpart_sender]
      have hs := TwoParty.run_sender (m := m)
        (rest := fun (_ : FoldMessage F G) => .node Fˣ (fun _ => protocolTree F G r))
        (rRest := fun _ => ⟨.receiver, fun _ => protocolRoles F G r⟩)
        (OutputP := fun _ => Unit) (OutputC := fun _ => Bool)
        (pure ⟨msg, fun x => pure (proverStrategy (next x))⟩)
        (fun msg => PublicCoinCounterpart.toCounterpart <$>
          pure (sample, fun x => publicVerifier sample (fold s msg x)))
      erw [hs, pure_bind, map_pure, pure_bind, PublicCoinCounterpart.toCounterpart_receiver]
      have hr := TwoParty.run_receiver (m := m) (rest := fun (_ : Fˣ) => protocolTree F G r)
        (rRest := fun _ => protocolRoles F G r)
        (OutputP := fun _ => Unit) (OutputC := fun _ => Bool)
        (fun x => pure (proverStrategy (next x)))
        (do
          let x ← sample
          pure ⟨x, PublicCoinCounterpart.toCounterpart (publicVerifier sample (fold s msg x))⟩)
      erw [hr]
      simp only [pure_bind, bind_assoc]
      rw [source]
      change _ = sample >>= fun x => simulateQ (fun _ => sample)
        (source (next x) (fun tail => observe
          ⟨transcriptPath (.step msg x tail), (), accepts s (.step msg x tail)⟩))
      erw [map_bind]
      erw [bind_assoc]
      apply congrArg (fun k => sample >>= k)
      funext x
      erw [bind_assoc]
      calc
        _ = (fun out => observe ⟨⟨msg, ⟨x, out.1⟩⟩, out.2⟩) <$>
            TwoParty.run (protocolTree F G r) (protocolRoles F G r)
              (proverStrategy (m := m) (next x))
              (PublicCoinCounterpart.toCounterpart (publicVerifier sample (fold s msg x))) := by
          erw [map_eq_bind_pure_comp]
          apply bind_congr
          intro out
          erw [pure_bind, map_pure]
          rfl
        _ = _ := ih (fold s msg x) (next x)
          (fun out => observe ⟨⟨msg, ⟨x, out.1⟩⟩, out.2⟩)

/-- Ordinary execution retains the full path and both parties' outputs. -/
theorem execution_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (sample : m Fˣ) {r : Nat} (s : Statement F G r) (p : Prover F G r) :
    TwoParty.run (protocolTree F G r) (protocolRoles F G r)
      (proverStrategy (m := m) p) (PublicCoinCounterpart.toCounterpart (publicVerifier sample s)) =
      simulateQ (fun _ => sample) (source p (fun tr =>
        (⟨transcriptPath tr, (), accepts s tr⟩ :
          (_tr : PFunctor.FreeM.Path (protocolTree F G r)) × Unit × Bool))) := by
  simpa only [id_map, id_eq] using run_observe sample s p id

/-- The comparison also preserves the challenge handler's final private state. -/
theorem execution_state_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {S : Type} (sample : StateT S m Fˣ)
    {r : Nat} (s : Statement F G r) (p : Prover F G r) (state : S) :
    (TwoParty.run (protocolTree F G r) (protocolRoles F G r)
      (proverStrategy (m := StateT S m) p)
      (PublicCoinCounterpart.toCounterpart (publicVerifier sample s))).run state =
      (simulateQ (fun _ => sample) (source p (fun tr =>
        (⟨transcriptPath tr, (), accepts s tr⟩ :
          (_tr : PFunctor.FreeM.Path (protocolTree F G r)) × Unit × Bool)))).run state :=
  congrFun (execution_eq sample s p) state

end InnerProduct.Execution

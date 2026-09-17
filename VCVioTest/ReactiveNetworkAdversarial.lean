/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.OneTimePad.Reactive.Separation
public import PolyFun.Interaction.UC.ReactiveNetwork.Serial

/-!
# Adversarial execution checks

These are counterexamples to removing semantic hypotheses: explicit delivery, sufficient
fuel, an empty serial queue, correct decryption, and reply-preserving shared-state laws.
The queued state used below is reachable from initialization under a FIFO prefix.
-/

public section

namespace VCVioTest.ReactiveNetworkAdversarial

open PFunctor Interaction.UC ReactiveProcess ReactiveNetwork ReactiveRuntime
  OneTimePad.Reactive OracleComp

attribute [local implicit_reducible] signature Response network effects ports
  serviceAnswer envAnswer DynSystem.DynComputation.ofFreeM

@[expose] def env : Environment Bool Bool Unit where
  choose := pure (true, ())
  observe _ _ view := pure (view.2 == some true)

@[expose] def system : CipherSystem Bool Bool Unit :=
  ⟨fun _ message => message, fun _ ciphertext => ciphertext⟩

@[expose] def ops : Operations Bool Bool Unit := realOperations system (fun _ => pure true)

@[expose] def impl := implementation env ops

/-- A complete token run observes the actual authenticated plaintext. -/
example : tokenExperiment (network Bool Bool Unit) impl (pure ()) 9 =
    pure (some (.returned true)) := rfl

/-- The same number of activations is insufficient for FIFO's two extra deliveries. -/
example : fifoExperiment (network Bool Bool Unit) impl (pure ()) (fifoSchedule.take 9) =
    pure none := rfl

/-- Stopping just before the environment's verdict retains a residual computation. -/
example : tokenExperiment (network Bool Bool Unit) impl (pure ()) 8 = pure none := rfl

/-- Serial FIFO transfers the successful observation through the generic prefix theorem. -/
example : serialExperiment (network Bool Bool Unit) impl (pure ()) 9 =
    pure (some (.returned true)) := by
  rw [serialExperiment_eq_tokenExperiment]
  rfl

/-- The serial comparison also preserves unfinished execution, not just completed verdicts. -/
example : serialExperiment (network Bool Bool Unit) impl (pure ()) 8 = pure none := by
  rw [serialExperiment_eq_tokenExperiment]
  rfl

/-- Repeatedly scheduling both actors without delivering cannot produce a reply. -/
example : fifoExperiment (network Bool Bool Unit) impl (pure ())
    [.node false, .node false, .node true, .node true, .node true,
      .node true, .node true, .node false, .node false] = pure none := rfl

/-- Private auxiliary state persists even when the transmitted message is unchanged. -/
@[expose] def memoryEnvironment (memory : Bool) : Environment Bool Bool Bool where
  choose := pure (true, memory)
  observe _ retained _ := pure retained

/-- Equal input messages need not give equal outcomes for different private environment states. -/
example (memory : Bool) : tokenExperiment (network Bool Bool Bool)
    (implementation (memoryEnvironment memory) ops) (pure ()) 9 =
      pure (some (.returned memory)) := by
  cases memory <;> rfl

/-- A pending message obtained by executing the environment's actual send. -/
@[expose] def queued : State (network Bool Bool Unit) Unit :=
  { initial (network Bool Bool Unit) () with
    localState := Function.update (fun id => ((network Bool Bool Unit).component id).init ()) false
      (.liftBind .receive fun packet =>
        .liftBind (.effect (.observe (true, ()) packet.2)) fun verdict => .pure (.returned verdict))
    pending := [.inl ⟨true, ⟨(), true⟩⟩]
    elapsed := 2 }

/-- The counterexample uses a reachable queue, not an arbitrary malformed state. -/
theorem queued_reachable :
    runFIFO impl [.node false, .node false] (initial (network Bool Bool Unit) ()) =
      pure queued := by
  apply congrArg (pure (f := ProbComp))
  congr 1
  funext id
  cases id <;> rfl

/-- FIFO consumes the outstanding packet, while token execution leaves it pending. -/
theorem serialRound_without_empty_queue :
    (fun state => state.pending.length) <$> serialRound impl queued = pure 0 ∧
      (fun state => state.pending.length) <$>
        (State.addElapsed 1 <$> activate impl .token queued.focus queued) = pure 1 := by
  exact ⟨rfl, rfl⟩

/-- The empty-queue premise cannot be deleted from the serial comparison theorem. -/
theorem serialRound_ne_token_with_pending :
    serialRound impl queued ≠ State.addElapsed 1 <$>
      activate impl .token queued.focus queued := by
  intro equal
  have projected := congrArg
    (fun program => (fun state => state.pending.length) <$> program) equal
  rw [serialRound_without_empty_queue.1, serialRound_without_empty_queue.2] at projected
  have distinguish := congrArg (fun program : ProbComp ℕ => Pr[= 0 | program]) projected
  simp at distinguish

/-- The finite-policy theorem also needs the empty-queue premise, even for one round. -/
example : runSerial impl 1 queued ≠ State.addElapsed 1 <$> runToken impl 1 queued := by
  simpa only [runSerial, runToken, bind_pure] using serialRound_ne_token_with_pending

/-- Incorrect decryption changes the environment's actual result. -/
example : tokenExperiment (network Bool Bool Unit)
    (implementation env (realOperations
      (CipherSystem.mk (fun _ message => message) (fun (_ : Unit) _ => false))
        (fun _ => pure true))) (pure ()) 9 = pure (some (.returned false)) := rfl

/-- A shared state operation returns the old state before flipping it. -/
@[expose] def flip : StateT Bool Id Bool := fun state => (state, !state)

/-- Reordering shared effects preserves the final state but swaps the clients' replies. -/
theorem shared_state_equality_does_not_preserve_replies :
    ((do let a ← flip; let b ← flip; pure (a, b) : StateT Bool Id (Bool × Bool)) false).2 =
      ((do let b ← flip; let a ← flip; pure (a, b) : StateT Bool Id (Bool × Bool)) false).2 ∧
    ((do let a ← flip; let b ← flip; pure (a, b) : StateT Bool Id (Bool × Bool)) false).1 ≠
      ((do let b ← flip; let a ← flip; pure (a, b) : StateT Bool Id (Bool × Bool)) false).1 := by
  exact ⟨rfl, by intro h; cases h⟩

/-! ## Concrete measurable observations

These finite, local instances witness that the security and separation statements apply
simultaneously to an observation space that distinguishes every terminal outcome.
-/

local instance : MeasurableSpace (BitVec 1) := ⊤
local instance : MeasurableSpace (Option (Outcome Bool)) := ⊤

/-- Cofree behavior preserves OTP simulation with private Boolean auxiliary state. -/
example (adversary : BitVec 1 → ProbComp Bool) :
    ∃ sim : Simulator (BitVec 1), ∀ env : Environment (BitVec 1) (BitVec 1) Bool,
      tokenLaw (network (BitVec 1) (BitVec 1) Bool).behavior
        (implementation env (realOperations (oneTimePad 1) adversary)) ($ᵗ BitVec 1) 9 =
      tokenLaw (network (BitVec 1) (BitVec 1) Bool).behavior
        (implementation env (idealOperations sim)) (pure 0) 9 := by
  obtain ⟨sim, hsim⟩ := oneTimePad_simulation 1 adversary
  refine ⟨sim, fun env => ?_⟩
  simpa only [tokenLaw_behavior] using (hsim Bool env).1

/-- The same fully distinguishing observation space rejects the leaking implementation. -/
example (sim : Simulator Bool) :
    tokenLaw (network Bool Bool Unit)
      (implementation leakEnvironment (realOperations leakingSystem (fun _ => pure false)))
        (pure ()) 9 ≠
      tokenLaw (network Bool Bool Unit) (implementation leakEnvironment (idealOperations sim))
        (pure false) 9 := leaking_tokenLaw_ne sim

end VCVioTest.ReactiveNetworkAdversarial

/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.CompressionCertificate
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Adaptive replacement of Foundation implementations

The handler retains a call count. Pointwise algorithm equality gives equality
of the joint response and state, which VCVio lifts to every adaptive client.
The compression service accepts valid byte windows and arbitrary chaining states.
The explicit word-level two-call experiment additionally samples its first input.
-/

public section

namespace Interop.Cryptol.Bridge

open OracleComp OracleSpec

/-- A word-input, word-output service. -/
abbrev wordSpec : OracleSpec UInt32 := fun _ => UInt32

/-- A deterministic implementation retaining the number of calls. -/
@[expose] def wordHandler (f : UInt32 → UInt32) : QueryImpl wordSpec (StateT Nat ProbComp) :=
  fun x state => pure (f x, state + 1)

/-- The implementations agree jointly on their response and retained state. -/
theorem wordHandler_joint_eq (x : UInt32) (state : Nat) :
    (wordHandler foundationSigma x).run state =ᵈ
      (wordHandler VCVio.Algorithms.Sha2.bsig0 x).run state := by
  change (pure (foundationSigma x, state + 1) : ProbComp (UInt32 × Nat)) =ᵈ
    pure (VCVio.Algorithms.Sha2.bsig0 x, state + 1)
  rw [foundationSigma_eq]

/-- Any adaptive client may replace one implementation with the other. -/
theorem simulate_wordHandler_eq {α : Type} (program : OracleComp wordSpec α) (state : Nat) :
    (simulateQ (wordHandler foundationSigma) program).run state =ᵈ
      (simulateQ (wordHandler VCVio.Algorithms.Sha2.bsig0) program).run state :=
  evalDistEq_simulateQ_run _ _ wordHandler_joint_eq program state

/-- The second input depends on the first response. -/
@[expose] def twoCalls (x : UInt32) : OracleComp wordSpec UInt32 := do
  let y : UInt32 ← wordSpec.query x
  wordSpec.query (x ^^^ y)

/-- Sample a full 32-bit input, then run an adaptive two-call client. -/
@[expose] def experiment (f : UInt32 → UInt32) : ProbComp (UInt32 × Nat) := do
  let x ← ProbComp.uniformFin (2 ^ 32 - 1)
  (simulateQ (wordHandler f) (twoCalls x.val.toUInt32)).run 0

/-- The sampled adaptive experiments have equal output distributions. -/
theorem experiment_eq : experiment foundationSigma =ᵈ
    experiment VCVio.Algorithms.Sha2.bsig0 :=
  EvalDistEq.bind_right _ fun x => simulate_wordHandler_eq (twoCalls x.val.toUInt32) 0

/-- Event probabilities transfer, including predicates on the retained state. -/
theorem experiment_event_eq (event : UInt32 × Nat → Prop) :
    Pr{let result ← experiment foundationSigma}[event result] =
      Pr{let result ← experiment VCVio.Algorithms.Sha2.bsig0}[event result] :=
  experiment_eq.prEvent_eq event

/-- A state/constant/schedule-word service returning the next eight registers. -/
abbrev roundSpec : OracleSpec RoundInput.Native := fun _ => RoundOutput.Native

/-- A round implementation with an explicit retained call counter. -/
@[expose] def roundHandler (f : RoundInput.Native → RoundOutput.Native) :
    QueryImpl roundSpec (StateT Nat ProbComp) := fun x state => pure (f x, state + 1)

/-- The extracted and VCVio rounds agree jointly on response and retained state. -/
theorem roundHandler_joint_eq (x : RoundInput.Native) (state : Nat) :
    (roundHandler (Foundation.round256.denote Interop.Cryptol.Finite.Env.empty) x).run state =ᵈ
      (roundHandler nativeRound x).run state := by
  change (pure (Foundation.round256.denote Interop.Cryptol.Finite.Env.empty x, state + 1) :
    ProbComp (RoundOutput.Native × Nat)) =ᵈ pure (nativeRound x, state + 1)
  rw [round256_native_eq]

/-- Every adaptive client may substitute one round implementation for the other. -/
theorem simulate_roundHandler_eq {α : Type} (program : OracleComp roundSpec α) (state : Nat) :
    (simulateQ (roundHandler (Foundation.round256.denote Interop.Cryptol.Finite.Env.empty))
      program).run state =ᵈ (simulateQ (roundHandler nativeRound) program).run state :=
  evalDistEq_simulateQ_run _ _ roundHandler_joint_eq program state

/-- A valid byte-window compression service. -/
abbrev compressionSpec : OracleSpec CompressionRequest := fun _ => Array UInt32

/-- Compression with an explicit retained call count. -/
@[expose] def compressionHandler (f : CompressionRequest → Array UInt32) :
    QueryImpl compressionSpec (StateT Nat ProbComp) :=
  fun request state => pure (f request, state + 1)

/-- Certified and byte-native implementations agree jointly on response and state. -/
theorem compressionHandler_joint_eq (request : CompressionRequest) (state : Nat) :
    (compressionHandler compiledCompress request).run state =ᵈ
      (compressionHandler nativeCompress request).run state := by
  change (pure (compiledCompress request, state + 1) : ProbComp (Array UInt32 × Nat)) =ᵈ
    pure (nativeCompress request, state + 1)
  rw [compiledCompress_eq]

/-- Arbitrary adaptive clients may replace all valid compression requests. -/
theorem simulate_compressionHandler_eq {α : Type}
    (program : OracleComp compressionSpec α) (state : Nat) :
    (simulateQ (compressionHandler compiledCompress) program).run state =ᵈ
      (simulateQ (compressionHandler nativeCompress) program).run state :=
  evalDistEq_simulateQ_run _ _ compressionHandler_joint_eq program state

/-- Replacement preserves events over the client's output and the retained state. -/
theorem compression_event_eq {α : Type} (program : OracleComp compressionSpec α)
    (state : Nat) (event : α × Nat → Prop) :
    Pr{let result ← (simulateQ (compressionHandler compiledCompress) program).run state}[
      event result] =
    Pr{let result ← (simulateQ (compressionHandler nativeCompress) program).run state}[
      event result] :=
  (simulate_compressionHandler_eq program state).prEvent_eq event

/-- A Boolean service for the retained-state counterexample. -/
abbrev bitSpec : OracleSpec Unit := fun _ => Bool

/-- Both services initially return false, but retain different next states. -/
@[expose] def hiddenStateHandler (next : Bool) : QueryImpl bitSpec (StateT Bool Id) :=
  fun _ state => pure (state, next)

/-- A second call observes the retained state. -/
@[expose] def readTwice : OracleComp bitSpec Bool := do
  let _ ← bitSpec.query ()
  bitSpec.query ()

/-- The first response alone does not distinguish the two services. -/
theorem first_response_eq :
    (hiddenStateHandler false ()).run' false = (hiddenStateHandler true ()).run' false := rfl

/-- Matching first responses is insufficient for matching adaptive executions. -/
theorem second_response_ne :
    (simulateQ (hiddenStateHandler false) readTwice).run' false ≠
      (simulateQ (hiddenStateHandler true) readTwice).run' false := by
  change false ≠ true
  decide

end Interop.Cryptol.Bridge

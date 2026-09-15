/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.OneTimePad.Separated.Execution
public import Examples.OneTimePad.Reactive.Security

/-!
# Perfect simulation with separated actors and an explicit backchannel

The real setup distributes two copies of its privately sampled key. The ideal setup sends
an independently sampled ciphertext to the sender and retains the input for the receiver.
Both systems use the same actual public channel, adversary, and environment backchannel.
Correct decryption and message-independent ciphertext laws imply equality of their executed
environment observations. The ideal ciphertext sampler is fixed before the environment.
-/

public section

namespace OneTimePad.Separated

open PFunctor Interaction.UC OracleComp MeasureTheory ProbabilityTheory

variable {Message Cipher Key Memory Advice : Type}

/-- Real endpoints receive the same private key and use the declared cipher system. -/
@[expose] def realEncoding (system : Reactive.CipherSystem Message Cipher Key) :
    Encoding Message Cipher Key Key Key where
  shares _ key := (key, key)
  encrypt := system.encrypt
  decrypt := system.decrypt

/-- The ideal service sends simulated ciphertext and preserves the input privately. -/
@[expose] def idealEncoding : Encoding Message Cipher Cipher Cipher Message where
  shares message ciphertext := (ciphertext, message)
  encrypt ciphertext _ := ciphertext
  decrypt message _ := message

variable [MeasurableSpace Message] [Countable Message] [MeasurableSingletonClass Message]
  [MeasurableSpace Cipher] [Countable Cipher] [MeasurableSingletonClass Cipher]
  [MeasurableSpace Memory] [Countable Memory] [MeasurableSingletonClass Memory]

/-- Ciphertext-law equality preserves input-dependent advice and subsequent delivery choices. -/
theorem conversation_simulation (system : Reactive.CipherSystem Message Cipher Key)
    (setup : ProbComp Key) (draw : ProbComp Cipher)
    (correct : ∀ key message, system.decrypt key (system.encrypt key message) = message)
    (secret : ∀ message, 𝒟[(fun key => system.encrypt key message) <$> setup] = 𝒟[draw])
    (adversary : Adversary Cipher Advice) (env : Environment Message Cipher Memory Advice) :
    𝒟[conversation (realEncoding system) setup env adversary] =
      𝒟[conversation idealEncoding draw env adversary] := by
  simp only [conversation, realEncoding, idealEncoding, correct]
  rw [evalDist_bind_of_discrete env.choose, evalDist_bind_of_discrete env.choose]
  apply Measure.bind_congr_right
  filter_upwards [] with input
  rw [show (setup >>= fun key => do
      let advice ← env.advise input.1 input.2 (system.encrypt key input.1)
      let permitted ← adversary.allow (system.encrypt key input.1) advice
      env.observe input.1 input.2 (system.encrypt key input.1)
        (if permitted then some input.1 else none)) =
      ((fun key => system.encrypt key input.1) <$> setup) >>= fun ciphertext => do
        let advice ← env.advise input.1 input.2 ciphertext
        let permitted ← adversary.allow ciphertext advice
        env.observe input.1 input.2 ciphertext (if permitted then some input.1 else none) from by
      rw [bind_map_left]]
  rw [evalDist_bind_of_discrete, secret, ← evalDist_bind_of_discrete]

/-- Perfect simulation compares the actual 29-activation executions of two six-actor networks. -/
theorem experiment_simulation (system : Reactive.CipherSystem Message Cipher Key)
    (setup : ProbComp Key) (draw : ProbComp Cipher)
    (correct : ∀ key message, system.decrypt key (system.encrypt key message) = message)
    (secret : ∀ message, 𝒟[(fun key => system.encrypt key message) <$> setup] = 𝒟[draw])
    (adversary : Adversary Cipher Advice) (env : Environment Message Cipher Memory Advice) :
    𝒟[experiment (realEncoding system) setup env adversary 29] =
      𝒟[experiment idealEncoding draw env adversary 29] := by
  rw [experiment_eq, experiment_eq, evalDist_map_of_discrete, evalDist_map_of_discrete,
    conversation_simulation system setup draw correct secret]

/-- OTP's named ideal sampler is uniform ciphertext, chosen independently of the environment. -/
theorem oneTimePad_experiment_simulation (width : ℕ)
    [MeasurableSpace (BitVec width)] [MeasurableSingletonClass (BitVec width)]
    (adversary : Adversary (BitVec width) Advice)
    (env : Environment (BitVec width) (BitVec width) Memory Advice) :
    𝒟[experiment (realEncoding (Reactive.oneTimePad width)) ($ᵗ BitVec width) env adversary 29] =
      𝒟[experiment idealEncoding ($ᵗ BitVec width) env adversary 29] := by
  apply experiment_simulation (Reactive.oneTimePad width)
  · intro key message
    simp [Reactive.oneTimePad]
  · intro message
    let e : BitVec width ≃ BitVec width :=
      ⟨fun key => key ^^^ message, fun key => key ^^^ message,
        fun key => by simp [BitVec.xor_assoc], fun key => by simp [BitVec.xor_assoc]⟩
    simpa only [bind_pure, ← map_eq_pure_bind, Reactive.oneTimePad, e, Equiv.coe_fn_mk] using
      (evalDist_bind_uniform_equiv ($ᵗ BitVec width) evalDist_uniformSample e
        (fun ciphertext => (pure ciphertext : ProbComp (BitVec width)))).symm

end OneTimePad.Separated

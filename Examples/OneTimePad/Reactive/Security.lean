/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.OneTimePad.Reactive
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Perfect simulation of single-use authenticated transmission

The simulator samples a ciphertext without a message argument, then runs the delivery
adversary on it. The ideal service retains the input privately and returns it only when
delivery is authorized. Correct decoding and a message-independent ciphertext law suffice
for equality of the actual environment outcome measures. The simulator is fixed before
quantifying over randomized environments and their countable private auxiliary state.

The result concerns the explicit two-actor, single-use delivery model in `Reactive`.
It does not provide a general UC context or computational-resource closure theorem.
-/

public section

namespace OneTimePad.Reactive

open PFunctor Interaction.UC ReactiveProcess ReactiveNetwork ReactiveRuntime
  OracleComp MeasureTheory ProbabilityTheory

variable {Message Cipher Key Memory : Type}

/-- A deterministic encryption/decryption pair, without assuming security or correctness. -/
structure CipherSystem (Message Cipher Key : Type) where
  /-- Encrypt using the private shared key. -/
  encrypt : Key → Message → Cipher
  /-- Decrypt using the same private shared key. -/
  decrypt : Key → Cipher → Message

/-- The actual encrypted service exposes only the ciphertext to its delivery adversary. -/
@[expose] def realOperations (system : CipherSystem Message Cipher Key)
    (adversary : Cipher → ProbComp Bool) : Operations Message Cipher Key where
  encrypt message key := pure (system.encrypt key message, key)
  allow ciphertext key := (fun permitted => (permitted, key)) <$> adversary ciphertext
  decrypt ciphertext key := pure (system.decrypt key ciphertext, key)

/-- Executable simulator access: generate public ciphertext, then decide delivery.
Neither operation receives the plaintext or the private setup. -/
structure Simulator (Cipher : Type) where
  /-- Sample the public ciphertext independently of the message. -/
  ciphertext : ProbComp Cipher
  /-- Simulate the adversary's delivery decision from that ciphertext. -/
  allow : Cipher → ProbComp Bool

/-- The ideal service stores the message privately while the simulator handles public traffic. -/
@[expose] def idealOperations (simulator : Simulator Cipher) :
    Operations Message Cipher Message where
  encrypt message _ := (fun ciphertext => (ciphertext, message)) <$> simulator.ciphertext
  allow ciphertext message := (fun permitted => (permitted, message)) <$> simulator.allow ciphertext
  decrypt _ message := pure (message, message)

/-- A simulator implemented by a fixed ciphertext sampler and the given delivery adversary. -/
@[expose] def simulator (draw : ProbComp Cipher) (adversary : Cipher → ProbComp Bool) :
    Simulator Cipher := ⟨draw, adversary⟩

/-- Direct encrypted execution retains decryption, so correctness is a separate obligation. -/
theorem conversation_realOperations (env : Environment Message Cipher Memory)
    (system : CipherSystem Message Cipher Key) (adversary : Cipher → ProbComp Bool) (key : Key) :
    conversation env (realOperations system adversary) key = (do
      let input ← env.choose
      let permitted ← adversary (system.encrypt key input.1)
      env.observe input.1 input.2 (system.encrypt key input.1,
        if permitted then some (system.decrypt key (system.encrypt key input.1)) else none)) := by
  simp [conversation, realOperations, apply_ite]

/-- Ideal decryption returns the input actually received, independently of the initial state. -/
theorem conversation_idealOperations (env : Environment Message Cipher Memory)
    (simulator : Simulator Cipher) (initialMessage : Message) :
    conversation env (idealOperations simulator) initialMessage = (do
      let input ← env.choose
      let ciphertext ← simulator.ciphertext
      let permitted ← simulator.allow ciphertext
      env.observe input.1 input.2 (ciphertext, if permitted then some input.1 else none)) := by
  simp [conversation, idealOperations, apply_ite]

/-- A terminal acceptance event is exactly the acceptance event of the executed conversation. -/
theorem tokenLaw_apply_returned [MeasurableSpace (Option (Outcome Bool))]
    [MeasurableSingletonClass (Option (Outcome Bool))]
    {S : Type} (env : Environment Message Cipher Memory) (ops : Operations Message Cipher S)
    (setup : ProbComp S) (verdict : Bool) :
    tokenLaw (network Message Cipher Memory) (implementation env ops) setup 9
        {some (.returned verdict)} =
      𝒟[setup >>= fun state => conversation env ops state] {verdict} := by
  rw [tokenLaw_eq_evalDist, tokenExperiment_eq]
  simp only [← map_bind]
  rw [evalDist_apply_singleton, evalDist_apply_singleton]
  exact probOutput_map_injective _
    (fun _ _ h => Outcome.returned.inj (Option.some.inj h)) verdict

variable [MeasurableSpace Memory] [Countable Memory] [MeasurableSingletonClass Memory]
  [MeasurableSpace Message] [Countable Message] [MeasurableSingletonClass Message]
  [MeasurableSpace Cipher] [Countable Cipher] [MeasurableSingletonClass Cipher]
  [MeasurableSpace Key] [Countable Key] [MeasurableSingletonClass Key]

/-- Correctness and message-independent ciphertext laws suffice for every environment verdict. -/
theorem conversation_simulation (system : CipherSystem Message Cipher Key)
    (setup : ProbComp Key) (draw : ProbComp Cipher)
    (correct : ∀ key message, system.decrypt key (system.encrypt key message) = message)
    (secret : ∀ message,
      𝒟[(fun key => system.encrypt key message) <$> setup] = 𝒟[draw])
    (adversary : Cipher → ProbComp Bool) (env : Environment Message Cipher Memory)
    (initialMessage : Message) :
    𝒟[setup >>= fun key => conversation env (realOperations system adversary) key] =
      𝒟[conversation env (idealOperations (simulator draw adversary)) initialMessage] := by
  simp only [conversation_realOperations, conversation_idealOperations, simulator, correct]
  rw [evalDist_bind_bind_swap setup env.choose _ (measurable_of_countable _)]
  rw [evalDist_bind_of_discrete env.choose, evalDist_bind_of_discrete env.choose]
  apply Measure.bind_congr_right
  filter_upwards [] with input
  rw [show (setup >>= fun key => adversary (system.encrypt key input.1) >>= fun permitted =>
      env.observe input.1 input.2
        (system.encrypt key input.1, if permitted then some input.1 else none)) =
      ((fun key => system.encrypt key input.1) <$> setup) >>= fun ciphertext =>
        adversary ciphertext >>= fun permitted =>
          env.observe input.1 input.2 (ciphertext, if permitted then some input.1 else none) from by
    rw [bind_map_left]]
  rw [evalDist_bind_of_discrete, secret, ← evalDist_bind_of_discrete]

/-- Perfect simulation observes actual terminal outcomes after token execution. -/
theorem tokenLaw_simulation [MeasurableSpace (Option (Outcome Bool))]
    (system : CipherSystem Message Cipher Key) (setup : ProbComp Key) (draw : ProbComp Cipher)
    (correct : ∀ key message, system.decrypt key (system.encrypt key message) = message)
    (secret : ∀ message,
      𝒟[(fun key => system.encrypt key message) <$> setup] = 𝒟[draw])
    (adversary : Cipher → ProbComp Bool) (env : Environment Message Cipher Memory)
    (initialMessage : Message) :
    tokenLaw (network Message Cipher Memory)
      (implementation env (realOperations system adversary)) setup 9 =
      tokenLaw (network Message Cipher Memory)
        (implementation env (idealOperations (simulator draw adversary)))
          (pure initialMessage) 9 := by
  rw [tokenLaw_eq_evalDist, tokenLaw_eq_evalDist, tokenExperiment_eq, tokenExperiment_eq]
  simp only [pure_bind, ← map_bind]
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete,
    conversation_simulation system setup draw correct secret]

/-- The single-use one-time pad uses the same XOR operation for encryption and decryption. -/
@[expose] def oneTimePad (width : ℕ) :
    CipherSystem (BitVec width) (BitVec width) (BitVec width) :=
  ⟨fun key message => key ^^^ message, fun key ciphertext => key ^^^ ciphertext⟩

/-- OTP has an executable simulator independent of the environment, for both disciplines. -/
theorem oneTimePad_simulation (width : ℕ)
    [MeasurableSpace (BitVec width)] [MeasurableSingletonClass (BitVec width)]
    [MeasurableSpace (Option (Outcome Bool))]
    (adversary : BitVec width → ProbComp Bool) :
    ∃ sim : Simulator (BitVec width),
      ∀ (Memory : Type) [MeasurableSpace Memory] [Countable Memory]
        [MeasurableSingletonClass Memory] (env : Environment (BitVec width) (BitVec width) Memory),
      tokenLaw (network (BitVec width) (BitVec width) Memory)
        (implementation env (realOperations (oneTimePad width) adversary)) ($ᵗ BitVec width) 9 =
        tokenLaw (network (BitVec width) (BitVec width) Memory)
          (implementation env (idealOperations sim)) (pure 0) 9 ∧
      fifoLaw (network (BitVec width) (BitVec width) Memory)
        (implementation env (realOperations (oneTimePad width) adversary))
          ($ᵗ BitVec width) fifoSchedule =
        fifoLaw (network (BitVec width) (BitVec width) Memory)
          (implementation env (idealOperations sim)) (pure 0) fifoSchedule := by
  refine ⟨simulator ($ᵗ BitVec width) adversary, fun Memory _ _ _ env => ?_⟩
  have secret (message : BitVec width) :
      𝒟[(fun key => (oneTimePad width).encrypt key message) <$> ($ᵗ BitVec width)] =
        𝒟[$ᵗ BitVec width] := by
    let e : BitVec width ≃ BitVec width :=
      ⟨fun key => key ^^^ message, fun key => key ^^^ message,
        fun key => by simp [BitVec.xor_assoc], fun key => by simp [BitVec.xor_assoc]⟩
    simpa only [bind_pure, ← map_eq_pure_bind, oneTimePad, e, Equiv.coe_fn_mk] using
      (evalDist_bind_uniform_equiv ($ᵗ BitVec width) evalDist_uniformSample e
        (fun ciphertext => (pure ciphertext : ProbComp (BitVec width)))).symm
  have ht := tokenLaw_simulation (oneTimePad width) ($ᵗ BitVec width) ($ᵗ BitVec width)
    (fun key message => by simp [oneTimePad]) secret adversary env 0
  refine ⟨ht, ?_⟩
  simpa only [fifoLaw_eq_evalDist, fifoExperiment_eq_tokenExperiment,
    ← tokenLaw_eq_evalDist] using ht

end OneTimePad.Reactive

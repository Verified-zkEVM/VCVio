/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.OneTimePad.Reactive.Security

/-!
# Negative semantic tests for authenticated transmission

A randomized environment recognizes plaintext leaked as ciphertext. Every simulator whose
ciphertext generation is independent of the message succeeds on this test with probability
one half, whereas the leaking implementation succeeds with probability one. Thus the
simulation interface does not make insecure services equivalent to the ideal service.
An independent counterexample retains uniform ciphertexts while returning the wrong plaintext.
Key reuse also separates joint ciphertext laws whose individual marginals are uniform.
-/

public section

namespace OneTimePad.Reactive

open Interaction.UC ReactiveProcess ReactiveNetwork ReactiveRuntime
  OracleComp MeasureTheory

/-- Choose a private random bit and test whether the public ciphertext reveals it. -/
@[expose] def leakEnvironment : Environment Bool Bool Unit where
  choose := (fun message => (message, ())) <$> ($ᵗ Bool)
  observe message _ view := pure (message == view.1)

/-- A correct but completely insecure encryption system. -/
@[expose] def leakingSystem : CipherSystem Bool Bool Unit :=
  ⟨fun _ message => message, fun _ ciphertext => ciphertext⟩

/-- Correct decryption alone does not imply secrecy. -/
theorem leakingSystem_correct (key : Unit) (message : Bool) :
    leakingSystem.decrypt key (leakingSystem.encrypt key message) = message := rfl

/-- The leaked plaintext is recognized even when delivery is denied. -/
theorem leaking_conversation_accepts :
    𝒟[conversation leakEnvironment (realOperations leakingSystem (fun _ => pure false)) ()]
      {true} = 1 := by
  rw [conversation_realOperations, evalDist_apply_singleton]
  simp [leakEnvironment, leakingSystem]

/-- No message-independent ciphertext simulator predicts the environment's random bit. -/
theorem ideal_conversation_accepts_half (sim : Simulator Bool) (initialMessage : Bool) :
    𝒟[conversation leakEnvironment (idealOperations sim) initialMessage] {true} = 1 / 2 := by
  rw [conversation_idealOperations, evalDist_apply_singleton]
  simpa [leakEnvironment, probOutput_bind_eq_tsum] using
    probOutput_decide_eq_uniformBool_half (fun _ => sim.ciphertext) rfl

/-- The actual leaking network is distinguishable from every allowed simulator. -/
theorem leaking_tokenLaw_ne [MeasurableSpace (Option (Outcome Bool))]
    [MeasurableSingletonClass (Option (Outcome Bool))] (sim : Simulator Bool) :
    tokenLaw (network Bool Bool Unit)
      (implementation leakEnvironment (realOperations leakingSystem (fun _ => pure false)))
        (pure ()) 9 ≠
      tokenLaw (network Bool Bool Unit) (implementation leakEnvironment (idealOperations sim))
        (pure false) 9 := by
  intro equal
  have event := congrArg (fun μ : Measure (Option (Outcome Bool)) =>
    μ {some (.returned true)}) equal
  simp only [tokenLaw_apply_returned, pure_bind, leaking_conversation_accepts,
    ideal_conversation_accepts_half] at event
  have hlt : (1 / 2 : ENNReal) < 1 := by
    rw [one_div, ENNReal.inv_lt_one]
    norm_num
  exact (ne_of_gt hlt) event

/-- The same attack distinguishes FIFO execution with all required deliveries present. -/
theorem leaking_fifoLaw_ne [MeasurableSpace (Option (Outcome Bool))]
    [MeasurableSingletonClass (Option (Outcome Bool))] (sim : Simulator Bool) :
    fifoLaw (network Bool Bool Unit)
      (implementation leakEnvironment (realOperations leakingSystem (fun _ => pure false)))
        (pure ()) fifoSchedule ≠
      fifoLaw (network Bool Bool Unit) (implementation leakEnvironment (idealOperations sim))
        (pure false) fifoSchedule := by
  simpa only [fifoLaw_eq_evalDist, fifoExperiment_eq_tokenExperiment,
    ← tokenLaw_eq_evalDist] using leaking_tokenLaw_ne sim

/-- Reusing a one-bit pad on zero and a second message exposes their XOR relation. -/
@[expose] def reusedPair (message : Bool) : ProbComp (Bool × Bool) :=
  (fun key => (key, key ^^ message)) <$> ($ᵗ Bool)

/-- The first projection of a reused pad has the original key law. -/
theorem evalDist_reusedPair_fst [EvalDistSemantics ProbComp] (message : Bool) :
    𝒟[Prod.fst <$> reusedPair message] = 𝒟[$ᵗ Bool] := by
  simp [reusedPair]

/-- The first projection of a reused pad has the original key law. -/
@[deprecated evalDist_reusedPair_fst (since := "2026-09-13")]
theorem reusedPair_first [EvalDistSemantics ProbComp] (message : Bool) :
    𝒟[Prod.fst <$> reusedPair message] = 𝒟[$ᵗ Bool] :=
  evalDist_reusedPair_fst message

/-- The second projection of a reused pad has the original key law when the key is uniform. -/
theorem evalDist_reusedPair_snd_of_uniform [EvalDistSemantics ProbComp]
    [LawfulEvalDistSemantics ProbComp]
    (hcoin : 𝒟[$ᵗ Bool] = ProbabilityTheory.uniformOn Set.univ) (message : Bool) :
    𝒟[Prod.snd <$> reusedPair message] = 𝒟[$ᵗ Bool] := by
  cases message with
  | false => simp [reusedPair]
  | true =>
      let e : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
      simpa [reusedPair, e] using
        (evalDist_map_equiv_of_uniform ($ᵗ Bool) hcoin e)

/-- The second projection of a reused pad has the original key law. -/
@[deprecated "Use evalDist_reusedPair_snd_of_uniform with a uniformity certificate"
  (since := "2026-09-13")]
theorem reusedPair_second (message : Bool) :
    𝒟[Prod.snd <$> reusedPair message] = 𝒟[$ᵗ Bool] :=
  evalDist_reusedPair_snd_of_uniform evalDist_uniformSample message

/-- Equal marginal ciphertext laws do not imply equal joint transcript laws. -/
theorem reusedPair_laws_ne : 𝒟[reusedPair false] ≠ 𝒟[reusedPair true] := by
  intro equal
  have event := congrArg (fun μ : Measure (Bool × Bool) => μ {pair | pair.1 = pair.2}) equal
  simp only [evalDist_apply_setOf] at event
  simp [reusedPair] at event

/-- Uniform ciphertexts with a deliberately incorrect decoder. -/
@[expose] def brokenDecoder : CipherSystem Bool Bool Bool :=
  ⟨fun key message => key ^^ message, fun _ _ => false⟩

/-- The broken decoder still satisfies the ciphertext secrecy premise of the positive theorem. -/
theorem brokenDecoder_ciphertext_uniform (message : Bool) :
    𝒟[(fun key => brokenDecoder.encrypt key message) <$> ($ᵗ Bool)] = 𝒟[$ᵗ Bool] := by
  simpa [reusedPair, brokenDecoder] using
    evalDist_reusedPair_snd_of_uniform evalDist_uniformSample message

/-- Ask for true and recognize delivery of the wrong plaintext, as distinct from dropping it. -/
@[expose] def wrongPlaintextEnvironment : Environment Bool Bool Unit where
  choose := pure (true, ())
  observe _ _ view := pure (view.2 == some false)

/-- Correct ciphertext secrecy cannot compensate for incorrect delivered plaintexts. -/
theorem brokenDecoder_accepts :
    𝒟[($ᵗ Bool) >>= fun key => conversation wrongPlaintextEnvironment
      (realOperations brokenDecoder (fun _ => pure true)) key] {true} = 1 := by
  rw [evalDist_apply_singleton]
  simp [conversation_realOperations, wrongPlaintextEnvironment, brokenDecoder]

/-- The ideal service can deliver the input or drop it, but cannot deliver a different plaintext. -/
theorem ideal_wrongPlaintext_rejects (sim : Simulator Bool) :
    𝒟[conversation wrongPlaintextEnvironment (idealOperations sim) false] {true} = 0 := by
  rw [conversation_idealOperations, evalDist_apply_singleton]
  simp [wrongPlaintextEnvironment, apply_ite]

/-- Dropping correctness from the simulation theorem is unsound even with uniform ciphertexts. -/
theorem brokenDecoder_tokenLaw_ne [MeasurableSpace (Option (Outcome Bool))]
    [MeasurableSingletonClass (Option (Outcome Bool))] (sim : Simulator Bool) :
    tokenLaw (network Bool Bool Unit)
      (implementation wrongPlaintextEnvironment
        (realOperations brokenDecoder (fun _ => pure true))) ($ᵗ Bool) 9 ≠
      tokenLaw (network Bool Bool Unit)
        (implementation wrongPlaintextEnvironment (idealOperations sim)) (pure false) 9 := by
  intro equal
  have event := congrArg (fun μ : Measure (Option (Outcome Bool)) =>
    μ {some (.returned true)}) equal
  simp only [tokenLaw_apply_returned, pure_bind, brokenDecoder_accepts,
    ideal_wrongPlaintext_rejects] at event
  exact one_ne_zero event

end OneTimePad.Reactive

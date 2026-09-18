/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.OneTimePad.Separated.Security
public import ToMathlib.MeasureTheory.DiscreteInstances

/-!
# Adversarial tests for separated OTP actors

These tests execute the complete six-component network. They distinguish an unfinished
prefix from a returned verdict, retain advice-dependent delivery, and show that a public
ciphertext-secrecy argument cannot compensate for an incorrect receiver.
-/

public section

namespace OneTimePad.Separated.Tests

open PFunctor Interaction.UC OracleComp MeasureTheory

@[expose] def encoding : Encoding Bool Bool Bool Bool Bool where
  shares _ key := (key, key)
  encrypt := Bool.xor
  decrypt := Bool.xor

@[expose] def env (message advice : Bool) : Environment Bool Bool Unit Bool where
  choose := pure (message, ())
  advise _ _ _ := pure advice
  observe message _ _ delivered := pure (delivered == some message)

@[expose] def adversary : Adversary Bool Bool := ⟨fun _ advice => pure advice⟩

/-- A correct receiver accepts precisely when the backchannel authorizes delivery. -/
example (message advice key : Bool) :
    experiment encoding (pure key) (env message advice) adversary 29 =
      pure (some (some advice)) := by
  cases message <;> cases advice <;> cases key <;> rfl

/-- The final observation operation is a real charged activation on both delivery branches. -/
example (message advice key : Bool) :
    experiment encoding (pure key) (env message advice) adversary 28 = pure none := by
  cases message <;> cases advice <;> cases key <;> rfl

/-- Ignoring the actual environment advice changes a fully executed delivery verdict. -/
example : 𝒟[experiment encoding (pure false) (env false true) adversary 29] ≠
    𝒟[experiment encoding (pure false) (env false false) adversary 29] := by
  change 𝒟[(pure (some (some true)) : ProbComp ReactiveSecurity.Result)] ≠
    𝒟[(pure (some (some false)) : ProbComp ReactiveSecurity.Result)]
  intro h
  have hevent := congrArg (fun μ : Measure ReactiveSecurity.Result => μ {some (some true)}) h
  simp at hevent

@[expose] def brokenEncoding : Encoding Bool Bool Bool Bool Bool :=
  { encoding with decrypt := fun key ciphertext => !(Bool.xor key ciphertext) }

/-- The sender's transformation is identical for the correct and broken receiver. -/
example : brokenEncoding.encrypt = encoding.encrypt := rfl

/-- Every pad exposes the incorrect receiver to an environment which checks its chosen message. -/
example (message key : Bool) :
    experiment brokenEncoding (pure key) (env message true) adversary 29 =
      pure (some (some false)) := by
  cases message <;> cases key <;> rfl

/-- Incorrect decryption breaks simulation against the same privately preserving ideal service. -/
example : 𝒟[experiment brokenEncoding (pure false) (env false true) adversary 29] ≠
    𝒟[experiment idealEncoding (pure false) (env false true) adversary 29] := by
  change 𝒟[(pure (some (some false)) : ProbComp ReactiveSecurity.Result)] ≠
    𝒟[(pure (some (some true)) : ProbComp ReactiveSecurity.Result)]
  intro h
  have hevent := congrArg (fun μ : Measure ReactiveSecurity.Result => μ {some (some true)}) h
  simp at hevent

/-- The correct receiver's completed observation is deterministic under every private pad law. -/
theorem correct_observation (message : Bool) (draw : ProbComp Bool) :
    𝒟[experiment encoding draw (env message true) adversary 29] =
      Measure.dirac (some (some true)) := by
  rw [experiment_eq]
  have hc : conversation encoding draw (env message true) adversary =
      (fun _ => true) <$> draw := by
    cases message <;> simp [conversation, encoding, env, adversary]
  rw [hc, Functor.map_map, evalDist_map_of_discrete]
  simp only [Measure.map_const, measure_univ, one_smul]

/-- The broken receiver is rejected even when its sender uses a uniformly random pad. -/
theorem broken_observation (message : Bool) (draw : ProbComp Bool) :
    𝒟[experiment brokenEncoding draw (env message true) adversary 29] =
      Measure.dirac (some (some false)) := by
  rw [experiment_eq]
  have hc : conversation brokenEncoding draw (env message true) adversary =
      (fun _ => false) <$> draw := by
    cases message <;> simp [conversation, brokenEncoding, encoding, env, adversary]
  rw [hc, Functor.map_map, evalDist_map_of_discrete]
  simp only [Measure.map_const, measure_univ, one_smul]

/-- Identical randomized encryption does not repair a semantically incorrect receiver. -/
example (message : Bool) :
    𝒟[experiment encoding ($ᵗ Bool) (env message true) adversary 29] ≠
      𝒟[experiment brokenEncoding ($ᵗ Bool) (env message true) adversary 29] := by
  rw [correct_observation, broken_observation]
  intro h
  have hevent := congrArg (fun μ : Measure ReactiveSecurity.Result => μ {some (some true)}) h
  simp at hevent

@[expose] def bitEnv (message advice : Bool) : Environment (BitVec 1) (BitVec 1) Unit Bool where
  choose := pure (if message then 1 else 0, ())
  advise _ _ _ := pure advice
  observe input _ _ delivered := pure (delivered == some input)

/-- The generic separated OTP theorem admits this concrete advice-driven environment. -/
example (message advice : Bool) :
    𝒟[experiment (realEncoding (Reactive.oneTimePad 1)) ($ᵗ BitVec 1)
      (bitEnv message advice) { allow := fun _ advice => pure advice } 29] =
      𝒟[experiment idealEncoding ($ᵗ BitVec 1)
        (bitEnv message advice) { allow := fun _ advice => pure advice } 29] :=
  oneTimePad_experiment_simulation 1 _ _

end OneTimePad.Separated.Tests

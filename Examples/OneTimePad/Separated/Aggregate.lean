/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.OneTimePad.Separated.Security

/-!
# Agreement with the aggregate delivery model

When advice depends only on ciphertext, the separated backchannel exchange can be included
in the aggregate delivery adversary. The two actual runtimes then have the same environment
observation law at their respective 29- and 9-activation budgets. The bridge does not erase
those different costs or claim that input-dependent backchannel advice belongs to the older
aggregate interface.
-/

public section

namespace OneTimePad.Separated

open PFunctor Interaction.UC OracleComp MeasureTheory

variable {Message Cipher Key Memory Advice : Type}

/-- Embed an aggregate environment with ciphertext-only backchannel advice. -/
@[expose] def Environment.ofReactive (env : Reactive.Environment Message Cipher Memory)
    (advice : Cipher → ProbComp Advice) : Environment Message Cipher Memory Advice where
  choose := env.choose
  advise _ _ ciphertext := advice ciphertext
  observe message memory ciphertext delivered := env.observe message memory (ciphertext, delivered)

/-- Include ciphertext-only advice in the aggregate adversary's delivery decision. -/
@[expose] def Adversary.toReactive (adversary : Adversary Cipher Advice)
    (advice : Cipher → ProbComp Advice) : Cipher → ProbComp Bool := fun ciphertext => do
  let response ← advice ciphertext
  adversary.allow ciphertext response

variable [MeasurableSpace Message] [Countable Message] [MeasurableSingletonClass Message]
  [MeasurableSpace Key] [Countable Key] [MeasurableSingletonClass Key]
  [MeasurableSpace Memory] [Countable Memory] [MeasurableSingletonClass Memory]

/-- Independent input and setup sampling commute in the restricted aggregate conversation. -/
theorem conversation_eq_aggregate (system : Reactive.CipherSystem Message Cipher Key)
    (setup : ProbComp Key) (env : Reactive.Environment Message Cipher Memory)
    (adversary : Adversary Cipher Advice) (advice : Cipher → ProbComp Advice) :
    𝒟[conversation (realEncoding system) setup (Environment.ofReactive env advice) adversary] =
      𝒟[setup >>= fun key => Reactive.conversation env
        (Reactive.realOperations system (adversary.toReactive advice)) key] := by
  simp only [conversation, realEncoding, Environment.ofReactive,
    Reactive.conversation_realOperations, Adversary.toReactive, bind_assoc]
  exact evalDist_bind_bind_swap env.choose setup _ (measurable_of_countable _)

/-- The separated and aggregate executions agree under the restricted backchannel policy,
with their distinct activation costs retained explicitly. -/
theorem experiment_eq_aggregate (system : Reactive.CipherSystem Message Cipher Key)
    (setup : ProbComp Key) (env : Reactive.Environment Message Cipher Memory)
    (adversary : Adversary Cipher Advice) (advice : Cipher → ProbComp Advice) :
    𝒟[experiment (realEncoding system) setup (Environment.ofReactive env advice) adversary 29] =
      𝒟[ReactiveSecurity.observe <$> ReactiveRuntime.tokenExperiment
        (Reactive.network Message Cipher Memory)
        (Reactive.implementation env (Reactive.realOperations system (adversary.toReactive advice)))
        setup 9] := by
  rw [experiment_eq, Reactive.tokenExperiment_eq]
  simp only [← map_bind, Functor.map_map]
  change 𝒟[(fun verdict => some (some verdict)) <$>
      conversation (realEncoding system) setup (Environment.ofReactive env advice) adversary] =
    𝒟[(fun verdict => some (some verdict)) <$> (setup >>= fun key =>
      Reactive.conversation env
        (Reactive.realOperations system (adversary.toReactive advice)) key)]
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, conversation_eq_aggregate]

end OneTimePad.Separated

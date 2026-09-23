/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveSecurity

/-!
# Executable real and ideal reactive worlds

A protocol exposes separate honest and adversarial boundaries. An adversary is an ordinary
handled assembly connected to the latter, with a separate backchannel to the environment.
An ideal-world simulator has the same backchannel and connects to the ideal functionality's
adversarial boundary. Both experiments execute the actual wired assemblies.

The statistical statements quantify over all finite closing contexts. Their witnesses are
executable fragments fixed before the closing environment and its execution horizon. They
do not assert uniformity across security parameters or polynomial resource bounds.
-/

public section

namespace Interaction.UC.ReactiveWorld

open ReactiveSecurity

variable {H A I J B : PortBoundary}

/-- A protocol or functionality with distinct honest and adversarial interfaces. -/
abbrev Protocol (honest adversarial : PortBoundary) :=
  System (PortBoundary.tensor honest adversarial)

/-- An executable adversary or simulator, with its own environment backchannel. -/
abbrev Adversary (adversarial backchannel : PortBoundary) :=
  System (PortBoundary.tensor (PortBoundary.swap adversarial) backchannel)

/-- Wire the adversarial interface, retaining honest traffic and the environment backchannel. -/
@[expose] def world (protocol : Protocol H A) (adversary : Adversary A B) :
    System (PortBoundary.tensor H B) := protocol.wire adversary

/-- The actual real or ideal experiment with the selected environment and finite horizon. -/
@[expose] def experiment (protocol : Protocol H A) (adversary : Adversary A B)
    (environment : Context (PortBoundary.tensor H B)) : ProbComp Result :=
  ReactiveSecurity.experiment (world protocol adversary) environment

/-- A named executable simulator bounds every finite environment's statistical advantage. -/
@[expose] def Simulates (error : ℝ) (real : Protocol H A) (ideal : Protocol H I)
    (adversary : Adversary A B) (simulator : Adversary I B) : Prop :=
  Contextual error (world real adversary) (world ideal simulator)

namespace Simulates

/-- Identical executable worlds admit the actual adversary as their zero-error simulator. -/
theorem refl (protocol : Protocol H A) (adversary : Adversary A B) :
    Simulates 0 protocol protocol adversary adversary := Contextual.refl _

/-- Chaining named executable simulators adds their statistical errors. -/
theorem trans {real : Protocol H A} {middle : Protocol H I} {ideal : Protocol H J}
    {adversary : Adversary A B} {first : Adversary I B} {second : Adversary J B}
    {error₁ error₂ : ℝ} (h₁ : Simulates error₁ real middle adversary first)
    (h₂ : Simulates error₂ middle ideal first second) :
    Simulates (error₁ + error₂) real ideal adversary second := Contextual.trans h₁ h₂

/-- A local contextual replacement remains valid after wiring the actual adversary. -/
theorem of_contextual {real ideal : Protocol H A} {error : ℝ}
    (h : Contextual error real ideal) (adversary : Adversary A B) :
    Simulates error real ideal adversary adversary := h.wire_left adversary

end Simulates

/-- Statistical emulation with an executable witness chosen before every closing environment.
The fixed boundaries are selected before execution and local private sampling. -/
@[expose] def StatisticallyEmulates (backchannel : PortBoundary) (error : ℝ)
    (real : Protocol H A) (ideal : Protocol H I) : Prop :=
  ∀ adversary : Adversary A backchannel,
    ∃ simulator : Adversary I backchannel, Simulates error real ideal adversary simulator

namespace StatisticallyEmulates

/-- The reflexive witness is the given executable adversary. -/
theorem refl (protocol : Protocol H A) : StatisticallyEmulates B 0 protocol protocol :=
  fun adversary => ⟨adversary, Simulates.refl protocol adversary⟩

/-- Emulation composes by feeding the first simulator to the second emulation theorem.
Both witnesses are fixed before the environment, and the two error bounds add. -/
theorem trans {real : Protocol H A} {middle : Protocol H I} {ideal : Protocol H J}
    {error₁ error₂ : ℝ} (h₁ : StatisticallyEmulates B error₁ real middle)
    (h₂ : StatisticallyEmulates B error₂ middle ideal) :
    StatisticallyEmulates B (error₁ + error₂) real ideal := by
  intro adversary
  obtain ⟨first, hfirst⟩ := h₁ adversary
  obtain ⟨second, hsecond⟩ := h₂ first
  exact ⟨second, hfirst.trans hsecond⟩

/-- Local replacement yields emulation with the original executable adversary as simulator. -/
theorem of_contextual {real ideal : Protocol H A} {error : ℝ}
    (h : Contextual error real ideal) : StatisticallyEmulates B error real ideal :=
  fun adversary => ⟨adversary, Simulates.of_contextual h adversary⟩

end StatisticallyEmulates

/-- Moving the adversary into the context preserves the complete probability experiment,
including honest-interface and backchannel traffic, at the same token horizon. -/
theorem experiment_factorization (protocol : Protocol H A) (adversary : Adversary A B)
    (environment : Context (PortBoundary.tensor H B)) :
    ReactiveSecurity.experiment protocol (environment.wireLeft adversary) =
      experiment protocol adversary environment :=
  experiment_wire_left protocol adversary environment

end Interaction.UC.ReactiveWorld

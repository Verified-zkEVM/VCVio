/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveWorld
public import VCVioTest.ReactiveSecurity

/-!
# Executed adversary and backchannel regressions

A server communicates through an ordinary bidirectional relay adversary. The environment
uses only the declared backchannel. The tests retain every relay activation and distinguish
the resulting execution from the direct exchange at an insufficient horizon.
-/

public section

namespace Interaction.UC.ReactiveWorld.Tests

open ReactiveSecurity ReactiveNetwork
open ReactiveSecurity.Tests (boundary server receiver context)

@[expose] def protocol (bit : Bool) : Protocol PortBoundary.empty boundary :=
  (server (pure bit)).map (PortBoundary.Equiv.tensorEmptyLeft boundary).symm.toHom

@[expose] def relay : Adversary boundary boundary := HandledAssembly.idWire boundary

@[expose] def environment (fuel : ℕ) :
    Context (PortBoundary.tensor PortBoundary.empty boundary) where
  system := receiver.map
    (PortBoundary.Equiv.tensorEmptyLeft (PortBoundary.swap boundary)).symm.toHom
  environment := ()
  fuel := fuel

/-- The actual relay carries both the request and response across the environment backchannel. -/
example (bit : Bool) :
    experiment (protocol bit) relay (environment 9) = pure (some (some bit)) := by
  cases bit <;> rfl

/-- Omitting the relay's four receive/send activations leaves the environment unfinished. -/
example (bit : Bool) : experiment (protocol bit) relay (environment 5) = pure none := by
  cases bit <;> rfl

/-- A forwarding adversary cannot be treated as a zero-cost identity at the same horizon. -/
theorem relay_changes_short_prefix (bit : Bool) :
    experiment (protocol bit) relay (environment 5) ≠
      ReactiveSecurity.experiment (server (pure bit)) (context 5) := by
  cases bit <;>
    change (pure none : ProbComp Result) ≠ pure (some (some _)) <;> simp

/-- The generic graph factorization consumes this concrete three-component execution. -/
example (bit : Bool) (fuel : ℕ) :
    ReactiveSecurity.experiment (protocol bit) ((environment fuel).wireLeft relay) =
      experiment (protocol bit) relay (environment fuel) :=
  experiment_factorization _ _ _

/-- The named reflexive simulator is the actual relay process and retains its forwarding cost. -/
example (bit : Bool) : Simulates 0 (protocol bit) (protocol bit) relay relay :=
  Simulates.refl _ _

end Interaction.UC.ReactiveWorld.Tests

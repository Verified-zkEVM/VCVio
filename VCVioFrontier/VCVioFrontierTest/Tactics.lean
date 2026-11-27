/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunFrontier.PFunctor.Free.Realization
import VCVio.CryptoFoundations.Asymptotics.ComplexityTactics
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-time tactic interoperability

Both tactic modules are in scope. VCVio selects an explicit quantitative realizer and
Frontier constructs a probabilistic machine proof for a fair coin.
-/

open PFunctor Turing.MultiTapeTM

example {S : StepClass} (Q : QuantitativeStepClass S) {α β : Type} (a : S.Str α) (b : S.Str β)
    (f : α → β) (h : Q.PolyRealizer a b f) : Q.PolyRealizer a b f := by
  ppt using h

example : Cslib.Probability.IsPPTOn encBits encBool
    (fun _ : List Bool => Cslib.ProbComp.uniform Bool) := by ppt []

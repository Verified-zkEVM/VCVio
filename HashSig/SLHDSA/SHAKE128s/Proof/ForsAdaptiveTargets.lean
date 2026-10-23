/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsCoverage

/-!
# Adaptive selection from an independent target tape

The policy decides whether to use target j from the preceding target values.
Disclosures are fixed and may include an entire padded honest-signing tape,
including its future disclosures. This file proves an expected-count bound for
this finite experiment, not a simulation theorem for the concrete shared ROM.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ForsAdaptiveTargets

abbrev View := ForsCoverage.View
abbrev Tape (trials : Nat) := Fin trials → View

end SlhDsaSecurity.ForsAdaptiveTargets

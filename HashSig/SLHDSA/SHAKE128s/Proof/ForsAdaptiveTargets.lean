/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsCoverage

/-!
# Adaptive selection from an independent target tape

The vocabulary of the finite adaptive-selection experiment: a `Tape` of independent uniform
FORS views, from which a policy decides whether to use target `j` based on the preceding target
values. Disclosures are fixed and may include an entire padded honest-signing tape, including its
future disclosures. The experiment is a finite model, not a simulation of the concrete shared
random oracle.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ForsAdaptiveTargets

/-- The parsed FORS view of one target. -/
abbrev View := ForsCoverage.View
/-- A tape of `trials` target views. -/
abbrev Tape (trials : Nat) := Fin trials → View

end SlhDsaSecurity.ForsAdaptiveTargets

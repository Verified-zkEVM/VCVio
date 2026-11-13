/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityExpandARO
import all LatticeCrypto.MLDSA.SecurityExpandARO

/-!
# Non-vacuity of the ML-DSA EUF-NMA bound with `ExpandA` a random oracle

- An aborting forger has advantage `0` in the `ExpandA` random-oracle game `romNmaAdvantage`
  (`romNmaAdvantage_aborting`), so the game is not one that every forger wins.
- `nma_security_rom` applies to that forger at arbitrary parameters, under the carrier instances
  the theorem itself assumes and with no further hypothesis.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto

namespace MLDSA.ExpandAROTest

open NMA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High] (M : Type) [DecidableEq M] [Inhabited M]

/-- An aborting forger has advantage `0` in the `ExpandA` random-oracle game. A game that ignored
the verifier, or accepted aborted signatures, would fail this. -/
theorem romNmaAdvantage_aborting :
    romNmaAdvantage p prims (M := M) (fun _ => pure (default, none)) = 0 := by
  simp [romNmaAdvantage, romNmaExperiment, verifyRO, withExpandACache, simulateToProbComp]

/-- `nma_security_rom` at the aborting forger. -/
example [NeZero p.gamma1] [Inhabited (Commitment p prims)] [Inhabited (Response p prims)] :
    romNmaAdvantage p prims (M := M) (fun _ => pure (default, none)) ≤
      LearningWithErrors.advantage (mldsaMatrixMLWE p)
          (distinguisherBRom p prims (M := M) fun _ => pure (default, none)) +
        SelfTargetMSIS.advantage (extractorCRom p prims (M := M) fun _ => pure (default, none)) :=
  nma_security_rom p prims _

end MLDSA.ExpandAROTest

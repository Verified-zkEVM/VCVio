/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ByteBound
public import HashSig.SLHDSA.Security.CoverageBound
public meta import HashSigTest.SLHDSA.Refactor.Capture

/-!
# Fully quantified signature contracts

The literal kernel types retain every parameter, sampling, model and resource quantifier.
Each command submits its source-constant witness to the ordinary checked declaration API.
Semantic dependency fingerprints protect the meaning of constants occurring in these types.
-/

public section

namespace SLHDSA.Refactor.R0

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.strongUnforgeableAdvantage_romScheme_pure_le_securityBound"
  as recoverStrongUnforgeableAdvantageRomSchemePureLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.securityTarget_two_one"
  as recoverSecurityTargetTwoOne

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.strongUnforgeableAdvantage_romScheme_le_securityBound"
  as recoverStrongUnforgeableAdvantageRomSchemeLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound"
  as recoverShakeStrongAdvantagePureLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero"
  as recoverShakeStrongAdvantagePureLeSecurityBoundOfWeakKeyMassEqZero

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32"
  as recoverShakeStrongAdvantagePureLeSecurityBoundOfNEq32

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le"
  as recoverShakeStrongAdvantagePureLeSecurityBoundOfPrEventOptRandLe

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged"
  as recoverShakeStrongAdvantagePureLeSecurityBoundHedged

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32"
  as recoverShakeStrongAdvantagePureLeSecurityBoundHedgedOfNEq32

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_min_of_n_eq_32"
  as recoverShakeStrongAdvantagePureLeMinOfNEq32

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32"
  as recoverShakeStrongAdvantagePureLeMinHedgedOfNEq32

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul"
  as recoverShakeStrongAdvantagePureLeSecurityBoundAddWeakKeyMassMul

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul"
  as recoverShakeStrongAdvantagePureLeSecurityBoundHedgedAddWeakKeyMassMul

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound"
  as recoverShakeStrongAdvantageLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged"
  as recoverShakeStrongAdvantageLeSecurityBoundHedged

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound_of_n_eq_32"
  as recoverShakeStrongAdvantageLeSecurityBoundOfNEq32

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_of_n_eq_32"
  as recoverShakeStrongAdvantageLeSecurityBoundHedgedOfNEq32

end SLHDSA.Refactor.R0

/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ByteBound
public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.Security.Profile
public import HashSig.SLHDSA.Security.Target
public import HashSig.SLHDSA.Security.Wire
public import VCVio.CryptoFoundations.SignatureAlg
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
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_validatedParams"
  as recoverShakeStrongAdvantagePureLeSecurityBoundValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams"
  as recoverShakeStrongAdvantagePureLeSecurityBoundHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_validatedParams"
  as recoverShakeStrongAdvantagePureLeSecurityBoundAddValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams"
  as recoverShakeStrongAdvantagePureLeSecurityBoundAddHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound_validatedParams"
  as recoverShakeStrongAdvantageLeSecurityBoundValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams"
  as recoverShakeStrongAdvantageLeSecurityBoundHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_pure_le_securityBound"
  as recoverShakeAdvantagePureLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_le_securityBound"
  as recoverShakeAdvantageLeSecurityBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_le_securityBound_hedged"
  as recoverShakeAdvantageLeSecurityBoundHedged

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_pure_le_securityBound_validatedParams"
  as recoverShakeAdvantagePureLeSecurityBoundValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_pure_le_securityBound_hedged_validatedParams"
  as recoverShakeAdvantagePureLeSecurityBoundHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_validatedParams"
  as recoverShakeAdvantagePureLeSecurityBoundAddValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_hedged_validatedParams"
  as recoverShakeAdvantagePureLeSecurityBoundAddHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_le_securityBound_validatedParams"
  as recoverShakeAdvantageLeSecurityBoundValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_le_securityBound_hedged_validatedParams"
  as recoverShakeAdvantageLeSecurityBoundHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeAdvantage_le_shakeStrongAdvantage"
  as recoverShakeAdvantageLeShakeStrongAdvantage

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.shakeStrongAdvantage_le_lintegral"
  as recoverShakeStrongAdvantageLeLintegral

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.unforgeableAdvantage_romScheme_le"
  as recoverUnforgeableAdvantageRomSchemeLe

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage"
  as recoverUnforgeableAdvantageLeStrongUnforgeableAdvantage

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.wireShakeScheme_map_shakeAnswer"
  as recoverWireShakeSchemeMapShakeAnswer

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.romQueryBound_wireReduce"
  as recoverRomQueryBoundWireReduce

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.wireStrongAdvantage_le"
  as recoverWireStrongAdvantageLe

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.wireStrongAdvantage_le_securityBound_validatedParams"
  as recoverWireStrongAdvantageLeSecurityBoundValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.wireStrongAdvantage_le_securityBound_hedged_validatedParams"
  as recoverWireStrongAdvantageLeSecurityBoundHedgedValidatedParams

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.ShakeProfile.strongUnforgeableAdvantage_le_boundEvaluator"
  as recoverStrongUnforgeableAdvantageLeBoundEvaluator

end SLHDSA.Refactor.R0

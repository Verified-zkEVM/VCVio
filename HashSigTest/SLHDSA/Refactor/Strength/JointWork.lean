/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Equality
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.QueryBudget
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget
public import HashSig.SLHDSA.SHAKE128s.Proof.WorkFinal
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.WireStrongUnforgeability
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
  for "SLHDSA.SHAKE128s.slhDsa_sufCma_127"
  as recoverSlhDsaSufCma127

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.Bridge.strongUnforgeableAdvantage_eq_fixedContext"
  as recoverStrongUnforgeableAdvantageEqFixedContext

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.Bridge.isTotalQueryBound_FIPS205_internal_verify"
  as recoverIsTotalQueryBoundFIPS205InternalVerify

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.Bridge.isTotalQueryBound_FIPS205_verify"
  as recoverIsTotalQueryBoundFIPS205Verify

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.Bridge.withinSigningLimit_fixedContext"
  as recoverWithinSigningLimitFixedContext

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.Bridge.hasQueryBound_fixedContext"
  as recoverHasQueryBoundFixedContext

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.wireStrongAdvantage_le_workBound"
  as recoverWireStrongAdvantageLeWorkBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.wireStrongAdvantage_le_min_bound"
  as recoverWireStrongAdvantageLeMinBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.WorkFinal.advantage_eq_zero"
  as recoverAdvantageEqZero

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.VerificationBudget.verification_count_bounds"
  as recoverVerificationCountBounds

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.VerificationBudget.verification_accepted_count_bounds"
  as recoverVerificationAcceptedCountBounds

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.SHAKE128s.VerificationBudget.accepted_outcome_work"
  as recoverAcceptedOutcomeWork

end SLHDSA.Refactor.R0

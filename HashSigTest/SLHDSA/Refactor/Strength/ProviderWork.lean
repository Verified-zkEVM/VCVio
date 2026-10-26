/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.GeneralSchemeQueryBound
public import HashSig.SLHDSA.SecretProvider
public import HashSig.SLHDSA.Security.BoundCertificates
public import HashSig.SLHDSA.Security.BoundEval
public import VCVio.CryptoFoundations.SignatureAlg.RomWork
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
  for "SLHDSA.forsRootWithSecret_eq_forsRootWith"
  as recoverForsRootWithSecretEqForsRootWith

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsPkGenWithSecret_eq_forsPkGenWith"
  as recoverForsPkGenWithSecretEqForsPkGenWith

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsRootWithSecret_natural"
  as recoverForsRootWithSecretNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsPkGenWithSecret_natural"
  as recoverForsPkGenWithSecretNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsSignWithSecret_eq_forsSignWith"
  as recoverForsSignWithSecretEqForsSignWith

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsSignWithSecret_natural"
  as recoverForsSignWithSecretNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.forsSignWithSecretM_natural"
  as recoverForsSignWithSecretMNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralHypertree.signWithSecretM_eq_signM"
  as recoverSignWithSecretMEqSignM

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralHypertree.rootWithSecretM_eq_rootM"
  as recoverRootWithSecretMEqRootM

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralHypertree.signWithSecretM_natural"
  as recoverSignWithSecretMNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralHypertree.rootWithSecretM_natural"
  as recoverRootWithSecretMNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM"
  as recoverSignInternalWithSecretRandomizerMEqSignInternalWithRandomizerM

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural"
  as recoverKeygenInternalWithSecretMNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural"
  as recoverSignInternalWithSecretRandomizerMNatural

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SignatureAlg.RomWorkBounds"
  as recoverRomWorkBounds

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SignatureAlg.isQueryBoundP_runWithSigningOracle"
  as recoverIsQueryBoundPRunWithSigningOracle

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SignatureAlg.isQueryBoundP_strongUnforgeableExperiment"
  as recoverIsQueryBoundPStrongUnforgeableExperiment

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralScheme.verifyInternalQueryBound"
  as recoverVerifyInternalQueryBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.GeneralScheme.verifyInternalM_isTotalQueryBound"
  as recoverVerifyInternalMIsTotalQueryBound

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.rationalValue_averagedByteBoundEval"
  as recoverRationalValueAveragedByteBoundEval

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.rationalValue_averagedByteBoundHedgedEval"
  as recoverRationalValueAveragedByteBoundHedgedEval

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.boundTable_certified"
  as recoverBoundTableCertified

slhdsa_r0_witness
  "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json"
  for "SLHDSA.Security.rangeCoefficients_certified"
  as recoverRangeCoefficientsCertified

end SLHDSA.Refactor.R0

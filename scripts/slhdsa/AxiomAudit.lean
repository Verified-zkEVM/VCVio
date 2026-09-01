/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# SLH-DSA load-bearing axiom audit

This elaboration gate resolves the curated load-bearing SLH-DSA roots and requires exact equality
of every transitive axiom footprint. The root names are unique, and the four footprint groups are
kept distinct so a declaration cannot silently acquire or lose a logical dependency.
-/

open Lean Elab Command

public meta section

namespace SLHDSAAxiomAudit

private def axiomFreeRoots : Array Name := #[
  ``SLHDSA.FipsParameterSet.ofParams_self,
  ``SLHDSA.CorePrimitives.ByteLaws.yToBytes_eq_iff,
  ``SLHDSA.Concrete.fips_hp_le_nine,
  ``SLHDSA.Security.GeneratedKeyPair,
  ``SLHDSA.Security.SchemeInterface,
  ``SLHDSA.Security.CollectionDisjoint
]

private def propextRoots : Array Name := #[
  ``SLHDSA.FipsParameterSet.params_valid,
  ``SLHDSA.FipsParameterSet.derived_widths_eq_expected,
  ``SLHDSA.FipsParameterSet.wots_widths,
  ``SLHDSA.decodeExact_encode,
  ``SLHDSA.base2b_bigEndian,
  ``SLHDSA.base2bChecked,
  ``SLHDSA.Adrs.isCanonical,
  ``SLHDSA.Adrs.decode,
  ``SLHDSA.Adrs.decode_encode,
  ``SLHDSA.decodePublicKey,
  ``SLHDSA.decodeSecretKey,
  ``SLHDSA.decodeSignature,
  ``SLHDSA.decodePublicKey_encode,
  ``SLHDSA.decodeSecretKey_encode,
  ``SLHDSA.decodeSignature_encode,
  ``SLHDSA.LayerPosition.initial,
  ``SLHDSA.LayerPosition.toAdrs_tree,
  ``SLHDSA.DigestParts.forsAdrs_tree,
  ``SLHDSA.DigestParts.forsAdrs_keyPair,
  ``SLHDSA.Security.targetEval_forsF_adrsToKey,
  ``SLHDSA.Security.targetEval_xmssH_adrsToKey,
  ``SLHDSA.Security.AdversaryBounds,
  ``SLHDSA.Security.honestTranscriptDistribution,
  ``SLHDSA.Security.SPprobSuccess,
  ``SLHDSA.Concrete.fips_decodeDigestParts_checked
]

private def proofRoots : Array Name := #[
  ``SLHDSA.toInt_eq_ofDigits,
  ``SLHDSA.Concrete.Keccak.shake256,
  ``SLHDSA.WotsEncoding.checksumByteLength_bits,
  ``SLHDSA.XmssConformance.TreePosition.index_lt_leafCount,
  ``SLHDSA.XmssConformance.honestClimbFips_eq_merkleRoot,
  ``SLHDSA.XmssConformance.honestClimbFips_eq_climb_authPath,
  ``SLHDSA.xmssNode_eq_merkleRoot,
  ``SLHDSA.DigestParts.idxTree_eq_zero_of_d_eq_one,
  ``SLHDSA.LayerPosition.tree_eq_zero_of_isFinal,
  ``SLHDSA.Security.encodeTargets_nodup_iff_injOn
]

private def standardRoots : Array Name := #[
  ``SLHDSA.toInt_lt_pow,
  ``SLHDSA.toInt_toByte_mod,
  ``SLHDSA.toInt_toByte,
  ``SLHDSA.toByteChecked_toInt,
  ``SLHDSA.Adrs.fromVector_toVector,
  ``SLHDSA.Adrs.fromVector_toVector_of_isCanonical,
  ``SLHDSA.Adrs.decode_toBytes,
  ``SLHDSA.Adrs.toWire_value,
  ``SLHDSA.Concrete.Sha2Address.compressSha2Checked_eq,
  ``SLHDSA.Concrete.Sha2Address.bytes_toList,
  ``SLHDSA.Concrete.sha2Primitives,
  ``SLHDSA.Concrete.shakePrimitives,
  ``SLHDSA.Concrete.approvedPrimitives,
  ``SLHDSA.Concrete.sha2Primitives_byteLaws,
  ``SLHDSA.Concrete.shakePrimitives_byteLaws,
  ``SLHDSA.Concrete.approvedPrimitives_byteLaws,
  ``SLHDSA.Concrete.Sha2.sha512,
  ``SLHDSA.WotsEncoding.shiftedChecksumValue_lt_pow,
  ``SLHDSA.WotsEncoding.checksumDigits_eq_digitsOfBaseW,
  ``SLHDSA.WotsEncoding.fullDigits_eq_wotsFullDigits,
  ``SLHDSA.chainLengthsCore_eq_wotsFullDigits,
  ``SLHDSA.chainLengthsCore_length,
  ``SLHDSA.chainLengthsCore_mem_lt,
  ``SLHDSA.wotsSkAdrs_isCanonical,
  ``SLHDSA.wotsChainHashAdrs_isCanonical,
  ``SLHDSA.wotsPkAdrs_isCanonical,
  ``SLHDSA.Concrete.sha2_wotsSkAdrs_isOk,
  ``SLHDSA.Concrete.sha2_wotsChainHashAdrs_isOk,
  ``SLHDSA.Concrete.sha2_wotsPkAdrs_isOk,
  ``SLHDSA.wotsPkFromSig_wotsSign,
  ``SLHDSA.XmssConformance.authPathVector_toList,
  ``SLHDSA.XmssConformance.authPathVector_get,
  ``SLHDSA.XmssConformance.wotsLeafAdrs_isCanonical,
  ``SLHDSA.XmssConformance.xmssNodeAdrs_isCanonical,
  ``SLHDSA.XmssConformance.xmssSignBounded_eq,
  ``SLHDSA.XmssConformance.xmssPkFromSigBounded_xmssSignBounded,
  ``SLHDSA.XmssConformance.xmssPkFromSigBounded_binding,
  ``SLHDSA.XmssConformance.xmssAuthPath_get,
  ``SLHDSA.Concrete.fips_nodePosition_fits,
  ``SLHDSA.Concrete.sha2_wotsLeafAdrs_isOk,
  ``SLHDSA.Concrete.sha2_xmssNodeAdrs_isOk,
  ``SLHDSA.Concrete.sha2_xmssWotsChainHashAdrs_isOk,
  ``SLHDSA.Concrete.shake_wotsLeafAdrs_roundtrip,
  ``SLHDSA.Concrete.shake_xmssNodeAdrs_roundtrip,
  ``SLHDSA.xmssSign_eq_mk,
  ``SLHDSA.xmssPkFromSig_xmssSign,
  ``SLHDSA.xmssPkFromSig_binding,
  ``SLHDSA.digestMdBytes_toList,
  ``SLHDSA.digestTreeBytes_toList,
  ``SLHDSA.digestLeafBytes_toList,
  ``SLHDSA.splitDigest_idxTree_val,
  ``SLHDSA.splitDigest_idxLeaf_val,
  ``SLHDSA.LayerPosition.next,
  ``SLHDSA.slhSignInternalM_isTotalQueryBound,
  ``SLHDSA.slhVerifyInternalM_isTotalQueryBound,
  ``SLHDSA.slhVerifyInternal_slhSignInternal,
  ``SLHDSA.LayerPosition.atLayer_zero_eq_initial,
  ``SLHDSA.LayerPosition.atLayer_succ_eq_next,
  ``SLHDSA.GeneralHypertree.signM_natural,
  ``SLHDSA.GeneralHypertree.pkFromSigM_natural,
  ``SLHDSA.GeneralHypertree.simulateQ_signM_withPublicHash,
  ``SLHDSA.GeneralHypertree.recoverFromPosition_signFromPosition,
  ``SLHDSA.GeneralHypertree.pkFromSig_sign,
  ``SLHDSA.GeneralScheme.signInternalM_natural,
  ``SLHDSA.GeneralScheme.verifyInternalM_natural,
  ``SLHDSA.GeneralScheme.verifyInternal_signInternal,
  ``SLHDSA.GeneralHypertree.signM_isTotalQueryBound,
  ``SLHDSA.GeneralHypertree.pkFromSigM_isTotalQueryBound,
  ``SLHDSA.GeneralScheme.signInternalM_isTotalQueryBound,
  ``SLHDSA.GeneralScheme.verifyInternalM_isTotalQueryBound,
  ``SLHDSA.DepthOneCompatibility.signM_toOneLayer_eq,
  ``SLHDSA.DepthOneCompatibility.signInternalM_toOneLayer_eq,
  ``SLHDSA.Security.sufAdvantage_eq_eufAdvantage_add_sameMessageAdvantage,
  ``SLHDSA.Security.allXmssTrees_length,
  ``SLHDSA.Security.forsLeafAddresses_length,
  ``SLHDSA.Security.xmssNodeAddresses_length,
  ``SLHDSA.Security.wotsStepAddresses_length_le_targetCount,
  ``SLHDSA.GeneralScheme.securityInterface_randomizer,
  ``SLHDSA.GeneralScheme.securityInterface_verify,
  ``SLHDSA.Security.RepairedMasterStatement,
  ``SLHDSA.Security.targetCount_pos,
  ``SLHDSA.Security.boolEventProbability,
  ``SLHDSA.Security.tcrProbability,
  ``SLHDSA.Security.tcrCProbability,
  ``SLHDSA.Security.dsprProbability,
  ``SLHDSA.Security.forsFSPprobability,
  ``SLHDSA.Security.preCProbability,
  ``SLHDSA.Security.wotsUDRealProbability,
  ``SLHDSA.Security.wotsUDIdealProbability,
  ``SLHDSA.Security.itsrComponentProbability,
  ``SLHDSA.Security.componentTerm,
  ``SLHDSA.Security.eufAdvantage,
  ``SLHDSA.Security.repairedRHS,
  ``SLHDSA.Security.sampledTargetRealImpl,
  ``SLHDSA.Security.CanonicalGames.wotsFPreCProblem_eval_adrsToKey,
  ``SLHDSA.Security.CanonicalGames.ReductionAdversaries,
  ``SLHDSA.Security.wotsPkGenM_traceContract,
  ``SLHDSA.Security.wotsSignM_traceContract,
  ``SLHDSA.Security.wotsPkFromSigM_traceContract,
  ``SLHDSA.Security.mem_logged_query_isConstructionReachable,
  ``SLHDSA.ForsConformance.decodeIndices_get_bigEndian,
  ``SLHDSA.ForsConformance.globalLeafIndex_decode_val,
  ``SLHDSA.ForsConformance.forsAuthPathVector_decode_get,
  ``SLHDSA.ForsConformance.forsSign_get_eq_decoded,
  ``SLHDSA.ForsConformance.forsNodeAdrs_isCanonical,
  ``SLHDSA.Concrete.fips_digestForsAdrs_isCanonical,
  ``SLHDSA.Concrete.sha2_digestForsAdrs_isOk,
  ``SLHDSA.Concrete.sha2_forsSkAdrs_isOk,
  ``SLHDSA.Concrete.sha2_forsNodeAdrs_isOk,
  ``SLHDSA.Concrete.sha2_forsPkAdrs_isOk,
  ``SLHDSA.GeneralHypertree.signFromPositionWith_one_recover,
  ``SLHDSA.GeneralHypertree.signFromPositionWith_two,
  ``SLHDSA.GeneralHypertree.signFromPositionWith_eq_signFromPositionM,
  ``SLHDSA.GeneralHypertree.recoverFromPositionWith_eq_recoverFromPositionM,
  ``SLHDSA.GeneralHypertree.simulateQ_signWith_publicHash,
  ``SLHDSA.GeneralHypertree.simulateQ_pkFromSigWith_publicHash,
  ``SLHDSA.HypertreeConformance.trace_succ,
  ``SLHDSA.Concrete.sha2_layerPosition_toAdrs_isOk,
  ``SLHDSA.Concrete.shake_layerPosition_toAdrs_roundtrip
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

private def expectedRoots : Array (Name × Array Name) :=
  axiomFreeRoots.map (·, #[]) ++
    propextRoots.map (·, #[``propext]) ++
    proofRoots.map (·, #[``propext, ``Quot.sound]) ++
    standardRoots.map (·, #[``propext, ``Classical.choice, ``Quot.sound])

run_cmd do
  unless expectedRoots.size == 160 do
    throwError "SLH-DSA axiom audit root count changed: expected 160, observed {expectedRoots.size}"
  let mut seen : Array Name := #[]
  for (root, expected) in expectedRoots do
    if seen.contains root then
      throwError "SLH-DSA axiom audit contains duplicate root {root}"
    seen := seen.push root
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "SLH-DSA axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"SLH-DSA axiom audit: PASS ({expectedRoots.size} unique exact roots; footprints 6/25/10/119)"

end SLHDSAAxiomAudit

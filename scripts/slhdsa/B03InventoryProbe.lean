/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig.SLHDSA.DepthOneCompatibility
public import HashSig.SLHDSA.GeneralSchemeQueryBound
public import HashSig.SLHDSA.Security.Architecture
public import HashSig.SLHDSA.Security.GeneralScheme
public import HashSig.SLHDSA.Security.ReachableTargets
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# B03 declaration and axiom-footprint probe

This elaboration gate resolves arbitrary-depth correctness, d=1 compatibility, naturality and
finite query-bound kernels, the exact SUF event partition, reachable structural target ledgers,
encoded-address compatibility equations, and the conditional general-scheme security interface.
It deliberately does not assert a security reduction.
-/

open Lean Elab Command

public meta section

namespace SLHDSAB03InventoryProbe

private def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def propextOnly : Array Name := #[``propext]

private def proofAxioms : Array Name := #[``propext, ``Quot.sound]

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.LayerPosition.atLayer_zero_eq_initial, standardAxioms),
  (``SLHDSA.LayerPosition.atLayer_succ_eq_next, standardAxioms),
  (``SLHDSA.GeneralHypertree.signM_natural, standardAxioms),
  (``SLHDSA.GeneralHypertree.pkFromSigM_natural, standardAxioms),
  (``SLHDSA.GeneralHypertree.simulateQ_signM_withPublicHash, standardAxioms),
  (``SLHDSA.GeneralHypertree.recoverFromPosition_signFromPosition, standardAxioms),
  (``SLHDSA.GeneralHypertree.pkFromSig_sign, standardAxioms),
  (``SLHDSA.GeneralScheme.signInternalM_natural, standardAxioms),
  (``SLHDSA.GeneralScheme.verifyInternalM_natural, standardAxioms),
  (``SLHDSA.GeneralScheme.verifyInternal_signInternal, standardAxioms),
  (``SLHDSA.GeneralHypertree.signM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.GeneralHypertree.pkFromSigM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.GeneralScheme.signInternalM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.GeneralScheme.verifyInternalM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.Security.targetEval_forsF_adrsToKey, propextOnly),
  (``SLHDSA.Security.targetEval_xmssH_adrsToKey, propextOnly),
  (``SLHDSA.DepthOneCompatibility.signM_toOneLayer_eq, standardAxioms),
  (``SLHDSA.DepthOneCompatibility.signInternalM_toOneLayer_eq, standardAxioms),
  (``SLHDSA.Security.sufAdvantage_eq_eufAdvantage_add_sameMessageAdvantage, standardAxioms),
  (``SLHDSA.Security.allXmssTrees_length, standardAxioms),
  (``SLHDSA.Security.forsLeafAddresses_length, standardAxioms),
  (``SLHDSA.Security.xmssNodeAddresses_length, standardAxioms),
  (``SLHDSA.Security.wotsStepAddresses_length_le_targetCount, standardAxioms),
  (``SLHDSA.Security.encodeTargets_nodup_iff_injOn, proofAxioms),
  (``SLHDSA.GeneralScheme.securityInterface_randomizer, standardAxioms),
  (``SLHDSA.GeneralScheme.securityInterface_verify, standardAxioms),
  (``SLHDSA.Security.RepairedMasterStatement, standardAxioms)
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "B03 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"B03 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAB03InventoryProbe

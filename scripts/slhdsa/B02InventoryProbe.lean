/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig.SLHDSA.Scheme
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# B02 PR #595 integration declaration and axiom-footprint probe

This elaboration gate resolves the load-bearing digest decomposition, typed hypertree-position,
FORS-address propagation, and retained d=1 Scheme roots imported at the B02 boundary.
-/

open Lean Elab Command

public meta section

namespace SLHDSAB02InventoryProbe

private def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def proofAxioms : Array Name :=
  #[``propext, ``Quot.sound]

private def propextOnly : Array Name := #[``propext]

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.digestMdBytes_toList, standardAxioms),
  (``SLHDSA.digestTreeBytes_toList, standardAxioms),
  (``SLHDSA.digestLeafBytes_toList, standardAxioms),
  (``SLHDSA.splitDigest_idxTree_val, standardAxioms),
  (``SLHDSA.splitDigest_idxLeaf_val, standardAxioms),
  (``SLHDSA.DigestParts.idxTree_eq_zero_of_d_eq_one, proofAxioms),
  (``SLHDSA.LayerPosition.initial, propextOnly),
  (``SLHDSA.LayerPosition.next, standardAxioms),
  (``SLHDSA.LayerPosition.tree_eq_zero_of_isFinal, proofAxioms),
  (``SLHDSA.LayerPosition.toAdrs_tree, propextOnly),
  (``SLHDSA.DigestParts.forsAdrs_tree, propextOnly),
  (``SLHDSA.DigestParts.forsAdrs_keyPair, propextOnly),
  (``SLHDSA.slhSignInternalM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.slhVerifyInternalM_isTotalQueryBound, standardAxioms),
  (``SLHDSA.slhVerifyInternal_slhSignInternal, standardAxioms)
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "B02 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"B02 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAB02InventoryProbe

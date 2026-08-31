/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig.SLHDSA.Concrete.Xmss
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# S06 declaration and axiom-footprint probe

This elaboration gate resolves the load-bearing bounded XMSS adapter, exact FIPS climb and
authentication-path equations, checked address boundaries, and retained canonical XMSS roots.
-/

open Lean Elab Command

public meta section

namespace SLHDSAS06InventoryProbe

private def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def proofAxioms : Array Name :=
  #[``propext, ``Quot.sound]

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.XmssConformance.TreePosition.index_lt_leafCount, proofAxioms),
  (``SLHDSA.XmssConformance.authPathVector_toList, standardAxioms),
  (``SLHDSA.XmssConformance.authPathVector_get, standardAxioms),
  (``SLHDSA.XmssConformance.honestClimbFips_eq_merkleRoot, proofAxioms),
  (``SLHDSA.XmssConformance.honestClimbFips_eq_climb_authPath, proofAxioms),
  (``SLHDSA.XmssConformance.wotsLeafAdrs_isCanonical, standardAxioms),
  (``SLHDSA.XmssConformance.xmssNodeAdrs_isCanonical, standardAxioms),
  (``SLHDSA.XmssConformance.xmssSignBounded_erase, standardAxioms),
  (``SLHDSA.XmssConformance.xmssPkFromSigBounded_xmssSignBounded, standardAxioms),
  (``SLHDSA.XmssConformance.xmssPkFromSigBounded_binding, standardAxioms),
  (``SLHDSA.XmssConformance.xmssAuthPath_get, standardAxioms),
  (``SLHDSA.Concrete.fips_hp_le_nine, #[]),
  (``SLHDSA.Concrete.fips_nodePosition_fits, standardAxioms),
  (``SLHDSA.Concrete.sha2_wotsLeafAdrs_isOk, standardAxioms),
  (``SLHDSA.Concrete.sha2_xmssNodeAdrs_isOk, standardAxioms),
  (``SLHDSA.Concrete.sha2_xmssWotsChainHashAdrs_isOk, standardAxioms),
  (``SLHDSA.Concrete.shake_wotsLeafAdrs_roundtrip, standardAxioms),
  (``SLHDSA.Concrete.shake_xmssNodeAdrs_roundtrip, standardAxioms),
  (``SLHDSA.xmssNode_eq_merkleRoot, proofAxioms),
  (``SLHDSA.xmssPkFromSig_xmssSign, standardAxioms),
  (``SLHDSA.xmssPkFromSig_binding, standardAxioms)
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "S06 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"S06 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAS06InventoryProbe

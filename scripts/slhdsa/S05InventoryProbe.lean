/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig.SLHDSA.Concrete.Wots
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# S05 declaration and axiom-footprint probe

This elaboration gate resolves the load-bearing FIPS WOTS+ byte-encoding, operational-equivalence,
address-boundary, and retained correctness roots and rejects changes to their exact transitive
axiom sets.
-/

open Lean Elab Command

public meta section

namespace SLHDSAS05InventoryProbe

private def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.WotsEncoding.checksumByteLength_bits, #[``propext, ``Quot.sound]),
  (``SLHDSA.WotsEncoding.shiftedChecksumValue_lt_pow, standardAxioms),
  (``SLHDSA.WotsEncoding.checksumDigits_eq_digitsOfBaseW, standardAxioms),
  (``SLHDSA.WotsEncoding.fullDigits_eq_wotsFullDigits, standardAxioms),
  (``SLHDSA.chainLengthsCore_eq_wotsFullDigits, standardAxioms),
  (``SLHDSA.chainLengthsCore_length, standardAxioms),
  (``SLHDSA.chainLengthsCore_mem_lt, standardAxioms),
  (``SLHDSA.wotsSkAdrs_isCanonical, standardAxioms),
  (``SLHDSA.wotsChainHashAdrs_isCanonical, standardAxioms),
  (``SLHDSA.wotsPkAdrs_isCanonical, standardAxioms),
  (``SLHDSA.Concrete.sha2_wotsSkAdrs_isOk, standardAxioms),
  (``SLHDSA.Concrete.sha2_wotsChainHashAdrs_isOk, standardAxioms),
  (``SLHDSA.Concrete.sha2_wotsPkAdrs_isOk, standardAxioms),
  (``SLHDSA.wotsPkFromSig_wotsSign, standardAxioms)
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "S05 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"S05 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAS05InventoryProbe

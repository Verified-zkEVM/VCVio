/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# S04 declaration and axiom-footprint probe

This elaboration gate resolves the S04 primitive roots and rejects changes to their exact
transitive axiom sets.
-/

open Lean Elab Command

public meta section

namespace SLHDSAS04InventoryProbe

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.Primitives.ByteLaws.yToBytes_eq_iff, #[]),
  (``SLHDSA.Concrete.Sha2Address.compressSha2Checked_eq,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.Sha2Address.bytes_toList,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.sha2Primitives, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.shakePrimitives, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.approvedPrimitives, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.sha2Primitives_byteLaws,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.shakePrimitives_byteLaws,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.approvedPrimitives_byteLaws,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.Sha2.sha512, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Concrete.Keccak.shake256, #[``propext, ``Quot.sound])
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "S04 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"S04 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAS04InventoryProbe

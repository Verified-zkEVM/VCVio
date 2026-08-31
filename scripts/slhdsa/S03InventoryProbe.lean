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
# S03 declaration and axiom-footprint probe

This elaboration gate resolves every S03 load-bearing inventory root and rejects any change to its
exact transitive axiom set. It complements the aggregate HashSig policy audit with per-root facts.
-/

open Lean Elab Command

public meta section

namespace SLHDSAS03InventoryProbe

private def roots : Array (Name × Array Name) := #[
  (``SLHDSA.FipsParameterSet.params_valid, #[``propext]),
  (``SLHDSA.FipsParameterSet.derived_widths_eq_expected, #[``propext]),
  (``SLHDSA.FipsParameterSet.wots_widths, #[``propext]),
  (``SLHDSA.FipsParameterSet.ofParams_self, #[]),
  (``SLHDSA.toInt_lt_pow, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.toInt_eq_ofDigits, #[``propext, ``Quot.sound]),
  (``SLHDSA.toInt_toByte_mod, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.toInt_toByte, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.toByteChecked_toInt, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.decodeExact_encode, #[``propext]),
  (``SLHDSA.base2b_bigEndian, #[``propext]),
  (``SLHDSA.base2bChecked, #[``propext]),
  (``SLHDSA.Adrs.isCanonical, #[``propext]),
  (``SLHDSA.Adrs.fromVector_toVector,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Adrs.fromVector_toVector_of_isCanonical,
    #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Adrs.decode, #[``propext]),
  (``SLHDSA.Adrs.decode_encode, #[``propext]),
  (``SLHDSA.Adrs.decode_toBytes, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.Adrs.toWire_value, #[``propext, ``Classical.choice, ``Quot.sound]),
  (``SLHDSA.decodePublicKey, #[``propext]),
  (``SLHDSA.decodeSecretKey, #[``propext]),
  (``SLHDSA.decodeSignature, #[``propext]),
  (``SLHDSA.decodePublicKey_encode, #[``propext]),
  (``SLHDSA.decodeSecretKey_encode, #[``propext]),
  (``SLHDSA.decodeSignature_encode, #[``propext])
]

private def sameNames (left right : Array Name) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

run_cmd do
  for (root, expected) in roots do
    let observed ← Lean.collectAxioms root
    unless sameNames observed expected do
      throwError "S03 axiom footprint changed for {root}: expected {expected}, observed {observed}"
  logInfo m!"S03 declaration/axiom probe: PASS ({roots.size} exact load-bearing roots)"

end SLHDSAS03InventoryProbe

/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Numeric
public import Lean.Data.Json

/-! # Executable numeric observations for comparison with pinned Cryptol -/

public section

namespace Interop.Cryptol.CLI

/-- Encode sizes as decimal strings, preserving arbitrary precision. -/
def numericLengthJson : Length → Lean.Json
  | .finite n => .str (toString n)
  | .infinite => .str "inf"

/-- Record undefined results separately from finite zero and infinity. -/
def numericCase (op : String) (args : List Length) (result : Option Length) : Lean.Json :=
  .mkObj [("op", .str op), ("arguments", .arr (args.map numericLengthJson).toArray),
    ("result", result.elim .null numericLengthJson)]

/-- Exercise boundary arithmetic at finite and infinite sizes. -/
def numericReport : Lean.Json := Id.run do
  let sizes := ([0, 1, 2, 7, 8, 17, 63, 64, 65].map Length.finite) ++ [.infinite]
  let binary : List (String × NumericBinary) :=
    [("add", .add), ("sub", .sub), ("mul", .mul), ("div", .div), ("mod", .mod),
      ("exp", .exp), ("min", .min), ("max", .max), ("ceilDiv", .ceilDiv), ("ceilMod", .ceilMod)]
  let unary : List (String × NumericUnary) := [("width", .width), ("lg2", .lg2)]
  let mut cases := #[]
  for (name, op) in binary do
    for a in sizes do
      for b in sizes do
        cases := cases.push (numericCase name [a, b] (op.eval a b))
  for (name, op) in unary do
    for a in sizes do
      cases := cases.push (numericCase name [a] (some (op.eval a)))
  for a in sizes do
    for b in sizes do
      for c in sizes do
        cases := cases.push (numericCase "rangeLength" [a, b, c] (numericRangeLength a b c))
  return .arr cases

end Interop.Cryptol.CLI

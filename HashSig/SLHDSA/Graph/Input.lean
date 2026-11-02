/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Children

/-!
# Natural structural inputs and returned-value cells

Inputs retain the full natural address and ordered current values of every child. Updating a
structural cell records the answer of that call and leaves the independent secret-seed cell alone.
-/

public section

namespace SLHDSA.Graph

/-- The full natural query label with its ordered current child values. -/
@[expose] def StructuralNode.input {p : Params} {Y : Type} (valid : p.Valid)
    (node : StructuralNode p) (cells : Node p → Y) : Adrs × List Y :=
  (node.address, (node.children valid).map cells)

/-- Update exactly the structural cell written by one actual query. -/
@[expose] def updateCell {p : Params} {Y : Type} (node : StructuralNode p)
    (cells : Node p → Y) (answer : Y) : Node p → Y :=
  Function.update cells (.structural node) answer

end SLHDSA.Graph

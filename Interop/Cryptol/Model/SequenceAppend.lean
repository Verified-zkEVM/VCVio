/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceOps
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Extending a lazy sequence by one suspended entry

The prefix and appended element need not be total. The equation identifies
concatenation with a shared finite prefix representation.
-/

public section

namespace Interop.Cryptol.Semantics

open OmegaCompletePartialOrder

/-- Appending a singleton retains partial entries without forcing either side. -/
theorem append_value_snoc {a : ClosedTy} {n : Nat}
    (xs : Fin n → Computation a) (x : Computation a) :
    append n (.finite 1) (.value xs) (.value (fun _ => x)) =
      .value (Fin.snoc xs x) := by
  apply congrArg DomainResult.value
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Length.add, Length.indexNat, indexAt, index_values, Length.checkIndex, Fin.snoc_last]
  · simp [Length.add, Length.indexNat, indexAt, index_values, Length.checkIndex,
      Fin.snoc_castSucc, j.isLt]

end Interop.Cryptol.Semantics

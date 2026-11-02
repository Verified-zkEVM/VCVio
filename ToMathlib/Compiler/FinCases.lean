/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module
public import Mathlib.Data.Fin.Basic

/-!
# Direct finite-index elimination for compilation

Importing this module installs the proved compiler simplification from `Fin.cases` to
`Fin.casesDirect`, whose implementation matches the index directly.
-/

public section

namespace Fin

/-- Dependent finite-index elimination by matching its zero and successor constructors. -/
@[expose] def casesDirect {n : Nat} {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) : ∀ i, motive i
  | ⟨0, hi⟩ => by rwa [Fin.mk_zero]
  | ⟨i + 1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The ordinary eliminator and its direct implementation agree for every dependent motive. -/
@[csimp] theorem cases_eq_casesDirect : @Fin.cases = @casesDirect := by
  funext n motive zero succ i
  rcases i with ⟨_ | i, hi⟩ <;> rfl

end Fin

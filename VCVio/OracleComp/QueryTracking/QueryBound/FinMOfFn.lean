/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import ToMathlib.Control.Monad.Fold

/-!
# Structural query bounds for finite sequencing

Sequencing `n` components with a uniform prefix bound `k` has prefix bound `n * k`.
Predicate-only query restrictions pass through the same traversal. These bounds also constrain
an issued query whose answer type is empty.
-/

public section

namespace OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- Uniform total query bounds add along finite monadic sequencing, including query prefixes. -/
theorem isTotalQueryBound_fin_mOfFn {n k : ℕ} (f : Fin n → OracleComp spec α)
    (hf : ∀ i, IsTotalQueryBound (f i) k) :
    IsTotalQueryBound (Fin.mOfFn n f) (n * k) := by
  induction n with
  | zero => simp [Fin.mOfFn, IsTotalQueryBound]
  | succ n ih =>
    simp only [Fin.mOfFn, Nat.succ_mul]
    rw [Nat.add_comm (n * k) k]
    apply isTotalQueryBound_bind (hf 0)
    intro value
    have htail := isTotalQueryBound_bind (n₂ := 0)
      (ih (fun i => f i.succ) (fun i => hf i.succ))
      (fun values : Fin n → α => (show IsTotalQueryBound
        (pure (Fin.cons (α := fun _ : Fin (n + 1) => α) value values) : OracleComp spec _)
          0 from trivial))
    simpa using htail

/-- Every query in a finite traversal satisfies a predicate when each component does. -/
theorem allQueriesSatisfy_fin_mOfFn {n : ℕ} (f : Fin n → OracleComp spec α)
    (P : ι → Prop) (hf : ∀ i, AllQueriesSatisfy (f i) P) :
    AllQueriesSatisfy (Fin.mOfFn n f) P := by
  induction n with
  | zero =>
    simp only [Fin.mOfFn]
    exact allQueriesSatisfy_pure _ _
  | succ n ih =>
    simp only [Fin.mOfFn]
    apply allQueriesSatisfy_bind (hf 0)
    intro value
    apply allQueriesSatisfy_bind (ih (fun i => f i.succ) (fun i => hf i.succ))
    intro values
    exact allQueriesSatisfy_pure _ _

end OracleComp

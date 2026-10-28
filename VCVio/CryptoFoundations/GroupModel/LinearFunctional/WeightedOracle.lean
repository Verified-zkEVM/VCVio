/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Weights
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! # Finite weighted queries to a shared oracle

A message may combine several oracle bases. The list preserves lookup order and repeated
labels; the standard random-oracle interpreter supplies the shared cache. No enumeration of
the label type is needed. Fixed-table interpretation commutes with the weighted sum.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Query each listed base and add its weighted contribution, in list order. -/
@[expose] def weightedQuery {F I V : Type} [Zero V] [Add V] [SMul F V] :
    List (I × F) → OracleComp (unifSpec + (I →ₒ V)) V
  | [] => pure 0
  | (i, a) :: rest => do
      let v : V ← (unifSpec + (I →ₒ V)).query (.inr i)
      let vs : V ← weightedQuery rest
      return a • v + vs

/-- The empty weighted query returns zero without querying the oracle. -/
@[simp] theorem weightedQuery_nil {F I V : Type} [Zero V] [Add V] [SMul F V] :
    weightedQuery (F := F) (I := I) (V := V) [] = pure 0 := rfl

/-- A nonempty weighted query first reads its leading base. -/
@[simp] theorem weightedQuery_cons {F I V : Type} [Zero V] [Add V] [SMul F V]
    (i : I) (a : F) (rest : List (I × F)) :
    weightedQuery (V := V) ((i, a) :: rest) = (do
      let v : V ← (unifSpec + (I →ₒ V)).query (.inr i)
      let vs : V ← weightedQuery rest
      return a • v + vs) := rfl

/-- A fixed oracle table evaluates a weighted query as the corresponding list sum. -/
theorem weightedQuery_table {F I V : Type} [AddMonoid V] [SMul F V]
    (table : I → V) (ts : List (I × F)) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table)) (weightedQuery ts) =
      pure ((ts.map fun t => t.2 • table t.1).sum) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rcases t with ⟨i, a⟩
      have hquery : unifFwdAnswerImpl (QueryImpl.ofFn table) (.inr i) =
          (pure (table i) : ProbComp V) := rfl
      simp [hquery, ih]

end GroupModel.LinearFunctional

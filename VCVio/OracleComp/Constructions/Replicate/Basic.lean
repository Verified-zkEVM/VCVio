/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.OracleComp
public import ToMathlib.Control.Monad.Fold

/-!
# Repeated oracle computations

`replicate` runs a computation a specified number of times, retaining its outputs in order.
`replicateTR` gives the equivalent tail-recursive traversal.
-/

public section

open OracleSpec

universe u v w

namespace OracleComp

/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
@[expose]
def replicate {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)

/-- Tail-recursive variant of `replicate`, running `oa` for each entry of a length-`n` list
built by `List.replicateTR`. Agrees with `replicate` via `replicateTR_eq_replicate`. -/
@[expose]
def replicateTR {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa

variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

@[simp, grind =]
lemma replicate_zero : replicate 0 oa = return [] := rfl

@[simp, grind =]
lemma replicateTR_zero : replicateTR 0 oa = return [] := rfl

/-- Bind-style unfolding of `replicate`, convenient for program-logic proofs. -/
@[simp, grind =]
lemma replicate_succ_bind :
    replicate (n + 1) oa = (do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)) := rfl

/-- The tail-recursive `replicateTR` agrees with the recursive `replicate`. The
`@[simp]` annotation lets every later proof about `replicateTR` reduce to the
recursive form automatically. -/
@[simp, grind =]
lemma replicateTR_eq_replicate : replicateTR n oa = replicate n oa := by
  simp only [replicateTR, ← List.replicate_eq_replicateTR]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, List.mapM_cons, ih]

lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  simp [replicate_succ_bind, monad_norm, Function.comp]

@[simp, grind =]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

end OracleComp

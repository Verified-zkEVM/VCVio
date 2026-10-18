/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold
public import ToMathlib.ProbabilityTheory.FinRatPMF.Basic
public import PolyFun.PFunctor.Bound

/-!
# Executable rational categorical sampling with persistent fair bits

A normalized `FinRatPMF.Raw` ticket array becomes a finite threshold client.
Its cumulative thresholds share one dyadic prefix. Zero weights and duplicate
outcomes are permitted, and the final ticket needs no threshold query. Every
new `sampleIO` call starts with an empty prefix and an injected bit source.
Measure correctness and finite-cap error bounds are in `Categorical.Semantics`.
-/

public section

open PFunctor

namespace UniformThreshold.Categorical

section Syntax

universe u
variable {α : Type u}

/-- Inspect cumulative rational thresholds, keeping one persistent random real. -/
@[expose] def scan (fallback : α) : ℚ → List (α × ℚ≥0) → FreeM spec.toPFunctor α
  | _, [] => pure fallback
  | _, [(value, _)] => pure value
  | lower, (value, weight) :: ticket :: rest => .liftBind (lower + weight) fun selected =>
      if selected then pure value else scan fallback (lower + weight) (ticket :: rest)

/-- A normalized ticket array contains an outcome, so sampling needs no `Inhabited` assumption. -/
@[expose] def fallback (distribution : FinRatPMF.Raw α) : α :=
  match h : distribution.toList with
  | [] => False.elim (by
      have hs : (distribution.toList.map Prod.snd).sum = 1 := distribution.sum_eq_one
      rw [h] at hs
      norm_num at hs)
  | (value, _) :: _ => value

/-- Compile the existing normalized rational distribution to a finite threshold client. -/
@[expose] def client (distribution : FinRatPMF.Raw α) : FreeM spec.toPFunctor α :=
  scan (fallback distribution) 0 distribution.toList

/-- A list of tickets needs at most one fewer threshold queries than its length. -/
theorem scan_query_bound (fallback : α) (lower : ℚ) (tickets : List (α × ℚ≥0)) :
    (scan fallback lower tickets).IsTotalRollBound (tickets.length - 1) := by
  induction tickets generalizing lower with
  | nil => trivial
  | cons ticket rest ih =>
      cases rest with
      | nil => trivial
      | cons next rest =>
          rcases ticket with ⟨value, weight⟩
          rw [scan, FreeM.isTotalRollBound_liftBind_iff]
          refine ⟨by simp, fun answer => ?_⟩
          cases answer
          · simpa only [List.length_cons, Nat.add_sub_cancel, Bool.false_eq_true, ↓reduceIte]
              using ih _
          · trivial

/-- Threshold queries are bounded without bounding the bit depth of an individual query. -/
theorem client_query_bound (distribution : FinRatPMF.Raw α) :
    (client distribution).IsTotalRollBound (distribution.toList.length - 1) :=
  scan_query_bound _ _ _

end Syntax

variable {α : Type}

/-- The common dispatcher implements the categorical client as a fair-bit machine. -/
@[expose] def compiled (distribution : FinRatPMF.Raw α) :=
  machineHandler.compile (fun _ : Unit => client distribution)

/-- Sample using an injected fair-bit source; all threshold arithmetic is rational. -/
def sampleIO (distribution : FinRatPMF.Raw α) (drawBit : IO Bool) : IO α := do
  let out ← (compiled distribution).runIO (ITree.withSilentSteps (fun _ => drawBit))
    ((compiled distribution).init ((), Prefix.empty))
  return out.1

end UniformThreshold.Categorical

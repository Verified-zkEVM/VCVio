/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import PolyFun.Control.Monad.Hom
public import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Bounded first-success search

An optional result advances the search precisely when it is `none`. An indexed sampler can
supply a different draw at each bounded position. Its result records the one-based successful
attempt and the ordered prefix consumed, including the full prefix on exhaustion. Monadic
failure and divergence are preserved by bind rather than converted to returned exhaustion.
-/

public section

namespace VCVio.Algorithms.FirstSuccess

universe u v w

/-- A bounded search returns a payload and attempt, or exhaustion, with its consumed draws. -/
inductive Result (R α : Type u) where
  | success (value : α) (attempt : ℕ) (consumed : List R)
  | exhausted (consumed : List R)
  deriving DecidableEq

namespace Result

/-- Observe a returned payload, retaining exhaustion as `none`. -/
@[expose] def output {R α : Type u} : Result R α → Option α
  | .success value _ _ => some value
  | .exhausted _ => none

/-- Observe the exact ordered list of draws consumed. -/
@[expose] def consumed {R α : Type u} : Result R α → List R
  | .success _ _ draws => draws
  | .exhausted draws => draws

/-- Observe the one-based successful attempt; exhaustion has no successful attempt. -/
@[expose] def attempt? {R α : Type u} : Result R α → Option ℕ
  | .success _ attempt _ => some attempt
  | .exhausted _ => none

/-- Map only the returned payload, preserving attempts, exhaustion and consumed draws. -/
@[expose] def map {R α β : Type u} (f : α → β) : Result R α → Result R β
  | .success value attempt draws => .success (f value) attempt draws
  | .exhausted draws => .exhausted draws

/-- Account for one failed draw before a recursive result. -/
@[expose] def prepend {R α : Type u} (draw : R) : Result R α → Result R α
  | .success value attempt draws => .success value (attempt + 1) (draw :: draws)
  | .exhausted draws => .exhausted (draw :: draws)

/-- Payload mapping commutes with the optional-output observation. -/
@[simp] theorem output_map {R α β : Type u} (f : α → β) (result : Result R α) :
    (result.map f).output = result.output.map f := by cases result <;> rfl

/-- Payload mapping preserves the consumed prefix. -/
@[simp] theorem consumed_map {R α β : Type u} (f : α → β) (result : Result R α) :
    (result.map f).consumed = result.consumed := by cases result <;> rfl

/-- Payload mapping preserves the successful-attempt observation. -/
@[simp] theorem attempt?_map {R α β : Type u} (f : α → β) (result : Result R α) :
    (result.map f).attempt? = result.attempt? := by cases result <;> rfl

/-- Mapping the identity leaves every returned result unchanged. -/
@[simp] theorem map_id {R α : Type u} (result : Result R α) :
    result.map id = result := by cases result <;> rfl

/-- Successive payload maps compose without changing observations. -/
theorem map_map {R α β γ : Type u} (f : α → β) (g : β → γ) (result : Result R α) :
    (result.map f).map g = result.map (g ∘ f) := by cases result <;> rfl

/-- Prepending a failed draw leaves the returned payload unchanged. -/
@[simp] theorem output_prepend {R α : Type u} (draw : R) (result : Result R α) :
    (result.prepend draw).output = result.output := by cases result <;> rfl

/-- Prepending a failed draw extends the consumed prefix at its beginning. -/
@[simp] theorem consumed_prepend {R α : Type u} (draw : R) (result : Result R α) :
    (result.prepend draw).consumed = draw :: result.consumed := by cases result <;> rfl

/-- Payload mapping commutes with accounting for a failed draw. -/
@[simp] theorem map_prepend {R α β : Type u} (f : α → β) (draw : R) (result : Result R α) :
    (result.prepend draw).map f = (result.map f).prepend draw := by cases result <;> rfl

end Result

variable {m : Type u → Type v} [Monad m] {R α β : Type u}

/-- Draw and classify up to a fixed budget, stopping at the first returned payload. -/
@[expose] def runWith (sample : m R) (accept : R → Option α) : ℕ → m (Option α)
  | 0 => pure none
  | n + 1 => do
    match accept (← sample) with
    | some value => pure (some value)
    | none => runWith sample accept n

/-- Repeat one optional computation until success or exhaustion of the budget. -/
@[expose] def run (attempt : m (Option α)) (budget : ℕ) : m (Option α) :=
  runWith attempt id budget

/-- A zero budget evaluates no draw and returns exhaustion. -/
@[simp] theorem runWith_zero (sample : m R) (accept : R → Option α) :
    runWith sample accept 0 = pure none := rfl

/-- A further attempt draws once, then either returns or continues. -/
theorem runWith_succ (sample : m R) (accept : R → Option α) (n : ℕ) :
    runWith sample accept (n + 1) =
      sample >>= fun draw => match accept draw with
        | some value => pure (some value)
        | none => runWith sample accept n := rfl

/-- A zero optional-computation budget returns exhaustion without executing it. -/
@[simp] theorem run_zero (attempt : m (Option α)) : run attempt 0 = pure none := rfl

/-- The optional-computation loop exposes its first attempt. -/
theorem run_succ (attempt : m (Option α)) (n : ℕ) :
    run attempt (n + 1) = attempt >>= fun result => match result with
      | some value => pure (some value)
      | none => run attempt n := rfl

/-- Draw at bounded increasing indices, recording the exact consumed prefix. -/
@[expose] def indexed (accept : R → Option α) :
    (budget : ℕ) → (Fin budget → m R) → m (Result R α)
  | 0, _ => pure (.exhausted [])
  | n + 1, sample => do
    let draw ← sample 0
    match accept draw with
    | some value => pure (.success value 1 [draw])
    | none => do
      let result ← indexed accept n (fun i => sample i.succ)
      pure (result.prepend draw)

/-- The indexed loop exposes its pure first draw and recursive suffix. -/
theorem indexed_id_succ (accept : R → Option α) (n : ℕ) (sample : Fin (n + 1) → R) :
    indexed (m := Id) accept (n + 1) sample =
      match accept (sample 0) with
      | some value => .success value 1 [sample 0]
      | none => (indexed (m := Id) accept n (fun i => sample i.succ)).prepend (sample 0) := rfl

/-- Pure indexed search consumes an ordered prefix within its budget. Success records its
positive prefix length as the one-based attempt; exhaustion consumes the complete budget. -/
theorem indexed_id_observations (accept : R → Option α) (budget : ℕ)
    (sample : Fin budget → R) :
    let result := indexed (m := Id) accept budget sample
    result.consumed = (List.ofFn sample).take result.consumed.length ∧
      result.consumed.length ≤ budget ∧
      match result with
      | .success _ attempt _ => attempt = result.consumed.length ∧ 0 < attempt
      | .exhausted _ => result.consumed.length = budget := by
  induction budget with
  | zero => exact ⟨rfl, Nat.le_refl 0, rfl⟩
  | succ budget ih =>
    rw [indexed_id_succ]
    cases hfirst : accept (sample 0) with
    | some value => simp [Result.consumed, List.ofFn_succ]
    | none =>
      have htail := ih (fun i => sample i.succ)
      cases ht : indexed (m := Id) accept budget (fun i => sample i.succ) with
      | success value attempt draws =>
        simp only [ht, Result.consumed] at htail
        simp only [Result.prepend, Result.consumed, List.length_cons, List.ofFn_succ,
          List.take_succ_cons]
        exact ⟨congrArg (List.cons (sample 0)) htail.1,
          Nat.succ_le_succ htail.2.1, by omega, by omega⟩
      | exhausted draws =>
        simp only [ht, Result.consumed] at htail
        simp only [Result.prepend, Result.consumed, List.length_cons, List.ofFn_succ,
          List.take_succ_cons]
        exact ⟨congrArg (List.cons (sample 0)) htail.1,
          Nat.succ_le_succ htail.2.1, by omega⟩

/-- Forgetting indexed metadata gives the constant-sampler search exactly. -/
theorem runWith_eq_output_indexed [LawfulMonad m]
    (sample : m R) (accept : R → Option α) (budget : ℕ) :
    runWith sample accept budget =
      Result.output <$> indexed accept budget (fun _ => sample) := by
  induction budget with
  | zero => simp [runWith, indexed, Result.output]
  | succ budget ih =>
    simp only [runWith, indexed, map_bind]
    congr 1
    funext draw
    cases h : accept draw with
    | some value => simp [Result.output]
    | none =>
      simpa only [map_bind, map_pure, Result.output_prepend, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind] using ih

/-- Classifying a draw before entering the optional loop preserves its computation. -/
theorem runWith_eq_run_map [LawfulMonad m]
    (sample : m R) (accept : R → Option α) (budget : ℕ) :
    runWith sample accept budget = run (accept <$> sample) budget := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    rw [runWith_succ, run_succ, bind_map_left]
    congr 1
    funext draw
    cases accept draw <;> simp [ih]

/-- Mapping a successful payload commutes with the bounded search. -/
theorem map_runWith [LawfulMonad m] (f : α → β)
    (sample : m R) (accept : R → Option α) (budget : ℕ) :
    Option.map f <$> runWith sample accept budget =
      runWith sample (fun draw => (accept draw).map f) budget := by
  induction budget with
  | zero => simp [runWith]
  | succ budget ih =>
    simp only [runWith, map_bind]
    congr 1
    funext draw
    cases accept draw <;> simp [ih]

/-- Payload mapping commutes with indexed search and retains all retry metadata. -/
theorem map_indexed [LawfulMonad m] (f : α → β) (accept : R → Option α)
    (budget : ℕ) (sample : Fin budget → m R) :
    Result.map f <$> indexed accept budget sample =
      indexed (fun draw => (accept draw).map f) budget sample := by
  induction budget with
  | zero => simp [indexed, Result.map]
  | succ budget ih =>
    simp only [indexed, map_bind]
    congr 1
    funext draw
    cases accept draw with
    | some value => simp [Result.map]
    | none =>
      simp only [Option.map_none, map_bind, map_pure, Result.map_prepend]
      simpa only [bind_map_left] using congrArg
        (fun search => search >>= fun result => pure (result.prepend draw))
        (ih (fun i => sample i.succ))

end VCVio.Algorithms.FirstSuccess

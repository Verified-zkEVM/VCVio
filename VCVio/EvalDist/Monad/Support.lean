/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.EvalDist.Defs.Support
public import VCVio.Prelude.Core

/-!
# Structural support under monadic operations

Pure, bind, and map preserve operational reachability through `ExactMonadAttach`.
Finite-support equations add enumeration assumptions without choosing probabilities.
-/

public section

universe u v

variable {α β : Type u} {m : Type u → Type v} [Monad m]


@[grind =] lemma support_pure [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (x : α) :
    support (pure x : m α) = {x} := MonadAttach.support_pure x

lemma mem_support_pure_iff [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (x y : α) :
    x ∈ support (pure y : m α) ↔ x = y := by grind
lemma mem_support_pure_iff' [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (x y : α) :
    x ∈ support (pure y : m α) ↔ y = x := by aesop

/-- `obtain`-friendly forward direction of `mem_support_pure_iff`: membership in the support
of a `pure` forces equality with the pure value. -/
lemma eq_of_mem_support_pure [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    {x y : α} (h : y ∈ support (pure x : m α)) : y = x := by
  simpa [mem_support_pure_iff] using h

@[simp, grind =]
lemma finSupport_pure [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] [HasEvalFinset m]
    [DecidableEq α] (x : α) : finSupport (pure x : m α) = {x} := by aesop

lemma mem_finSupport_pure_iff [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ x = y := by grind
lemma mem_finSupport_pure_iff' [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ y = x := by aesop


@[grind =]
lemma support_bind [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) :=
  MonadAttach.support_bind mx my

@[grind =]
lemma mem_support_bind_iff [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (mx : m α)
    (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

/-- `obtain`-friendly forward direction of `mem_support_bind_iff`: peel an element of the
support of a bind into a witness for the first computation and membership for the second. -/
lemma support_bind_exists [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    {x : m α} {f : α → m β} {y : β}
    (hy : y ∈ support (x >>= f)) : ∃ a, a ∈ support x ∧ y ∈ support (f a) := by
  simpa [mem_support_bind_iff] using hy

@[simp, grind =]
lemma finSupport_bind [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) : finSupport (mx >>= my) =
      Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop

@[grind =]
lemma mem_finSupport_bind_iff [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) (y : β) : y ∈ finSupport (mx >>= my) ↔
      ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop


@[grind =]
lemma support_map [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by
  exact MonadAttach.support_map f mx

@[simp, grind =]
lemma finSupport_map [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (mx : m α) : finSupport (f <$> mx) = (finSupport mx).image f := by
  grind [map_eq_bind_pure_comp]


section forall_support

variable [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

@[simp] lemma allOutputsSatisfy_pure (p : α → Prop) (x : α) :
    allOutputsSatisfy p (pure x : m α) ↔ p x := by
  simp [allOutputsSatisfy]

@[simp] lemma someOutputSatisfies_pure (p : α → Prop) (x : α) :
    someOutputSatisfies p (pure x : m α) ↔ p x := by
  simp [someOutputSatisfies]

@[simp] lemma allOutputsSatisfy_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    allOutputsSatisfy p (mx >>= my) ↔
      allOutputsSatisfy (fun a => allOutputsSatisfy p (my a)) mx := by
  simp only [allOutputsSatisfy, support_bind]
  aesop

@[simp] lemma someOutputSatisfies_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    someOutputSatisfies p (mx >>= my) ↔
      someOutputSatisfies (fun a => someOutputSatisfies p (my a)) mx := by
  simp only [someOutputSatisfies, support_bind]
  aesop

end forall_support

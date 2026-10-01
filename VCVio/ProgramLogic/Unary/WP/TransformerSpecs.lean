/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Do.Spec

/-!
# Specifications of the transformers' constructors, lifts, runners and loops

Core registers the triples of the transformers' operations (`get`, `set`, `monadLift`, `throw`,
`tryCatch`, …) and of running an `OptionT` or `ExceptT` into the postcondition it pushes
(`Spec.run_OptionT`, `Spec.run_ExceptT`). The rules here cover what programs also write: the
constructors `StateT.mk`, `OptionT.mk` and `ExceptT.mk`, the lifts `StateT.lift` and
`ExceptT.lift`, running a `StateT` at a state with the state discarded, running an `OptionT` or
`ExceptT` into a postcondition of the option or the result, `List.mapM` with a loop invariant,
and the sequence combinators `<*` and `*>`. Each is a core triple of any `WPMonad`, so `vcgen`
uses it in every reading, through the transformer's interpretation of the base monad's.

`StateT.run x s` is `x s` once `vcgen` has unfolded the reducible constants of its goal, so no
rule can be keyed on it; a `StateT` program run at a state is reasoned about as a triple of the
program itself, with state-passing assertions (`StateT.wp_apply_eq`).
-/

public section

namespace Std.WP

open Lean.Order

universe u v w w' z

/-! ## `StateT`

Core's transformer interpretations keep the assertion languages in the universe of the monad's
values. -/

section StateT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type u}

/-- `StateT.lift x` is `monadLift x`: the base computation runs at the incoming state. -/
@[spec]
theorem Spec.lift_StateT (x : m α) (post : α → σ → Pred) {epost : EPred} :
    ⦃ fun s => wp x (fun a => post a s) epost ⦄ (StateT.lift x : StateT σ m α) ⦃ post; epost ⦄ :=
  Spec.monadLift_StateT x post

/-- `StateT.mk f` runs `f` at the incoming state. -/
@[spec]
theorem Spec.mk_StateT (f : σ → m (α × σ)) (post : α → σ → Pred) {epost : EPred} :
    ⦃ fun s => wp (f s) (fun p => post p.1 p.2) epost ⦄ (StateT.mk f : StateT σ m α)
      ⦃ post; epost ⦄ :=
  ⟨fun _ => PartialOrder.rel_refl⟩

/-- Running a `StateT` computation at a state and discarding the final state. -/
@[spec]
theorem Spec.run'_StateT (x : StateT σ m α) (s : σ) (post : α → Pred) {epost : EPred} :
    ⦃ wp x (fun a _ => post a) epost s ⦄ x.run' s ⦃ post; epost ⦄ :=
  ⟨by
    rw [StateT.wp_apply_eq]
    exact WPMonad.map_le_wp_map (fun p : α × σ => p.1) (x.run s) post epost⟩

end StateT

/-! ## `OptionT`

Running an `OptionT` computation into a postcondition of the option: core's `Spec.run_OptionT`
states the postcondition it pushes, so it applies when the goal's postcondition has that shape;
the rule here takes any postcondition and outranks it. -/

section OptionT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u}

/-- `OptionT.mk x` is the base computation `x`, read through the option it returns. -/
@[spec]
theorem Spec.mk_OptionT (x : m (Option α)) (post : α → Pred) (epost : (Unit → Pred) × EPred) :
    ⦃ wp x (pushOption post epost.fst) epost.snd ⦄ OptionT.mk x ⦃ post; epost ⦄ :=
  ⟨by rw [OptionT.wp_apply_eq]; exact PartialOrder.rel_refl⟩

/-- Running an `OptionT` computation into a postcondition of the returned option: success
establishes it at `some`, failure at `none`. -/
@[spec high]
theorem Spec.run_OptionT' (x : OptionT m α) (post : Option α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => post (some a)) (fun _ => post none, epost) ⦄ x.run ⦃ post; epost ⦄ :=
  ⟨by
    rw [OptionT.wp_apply_eq]
    have h : pushOption (fun a => post (some a)) (fun _ => post none) = post := by
      funext o; cases o <;> rfl
    rw [h]⟩

end OptionT

/-! ## `ExceptT` -/

section ExceptT

variable {m : Type u → Type v} {Pred EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {ε α : Type u}

/-- `ExceptT.lift x` is `monadLift x`: the base computation runs and succeeds. -/
@[spec]
theorem Spec.lift_ExceptT (x : m α) (post : α → Pred) (epost : (ε → Pred) × EPred) :
    ⦃ wp x post epost.snd ⦄ (ExceptT.lift x : ExceptT ε m α) ⦃ post; epost ⦄ :=
  Spec.monadLift_ExceptT x post epost

/-- `ExceptT.mk x` is the base computation `x`, read through the result it returns. -/
@[spec]
theorem Spec.mk_ExceptT (x : m (Except ε α)) (post : α → Pred) (epost : (ε → Pred) × EPred) :
    ⦃ wp x (pushExcept post epost.fst) epost.snd ⦄ ExceptT.mk x ⦃ post; epost ⦄ :=
  ⟨by rw [ExceptT.wp_apply_eq]; exact PartialOrder.rel_refl⟩

/-- Running an `ExceptT` computation into a postcondition of the returned result: success
establishes it at `ok`, an exception at `error`. -/
@[spec high]
theorem Spec.run_ExceptT' (x : ExceptT ε m α) (post : Except ε α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => post (.ok a)) (fun e => post (.error e), epost) ⦄ x.run ⦃ post; epost ⦄ :=
  ⟨by
    rw [ExceptT.wp_apply_eq]
    have h : pushExcept (fun a => post (.ok a)) (fun e => post (.error e)) = post := by
      funext r; cases r <;> rfl
    rw [h]⟩

end ExceptT

/-! ## `guard` -/

section guard

variable {m : Type → Type v} {Pred EPred : Type}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- `guard p` in `OptionT`: the postcondition when `p` holds and the failure assertion when it
does not, stated with lattice connectives so that every reading decomposes it. Core's
`Spec.guard_OptionT` is stated for `Prop` assertions and takes precedence there. -/
@[spec low]
theorem Spec.guard_OptionT_iInf (p : Prop) [Decidable p] (post : Unit → Pred)
    (epost : (Unit → Pred) × EPred) :
    ⦃ (Lean.Order.iInf fun _ : PLift p => post ()) ⊓
        (Lean.Order.iInf fun _ : PLift ¬p => epost.1 ()) ⦄ (guard p : OptionT m Unit)
      ⦃ post; epost ⦄ := by
  rw [Triple.iff]
  unfold guard
  split_ifs with hp
  · exact PartialOrder.rel_trans (meet_le_left _ _)
      (PartialOrder.rel_trans (iInf_le _ ⟨hp⟩) (Spec.pure ()).le_wp)
  · exact PartialOrder.rel_trans (meet_le_right _ _)
      (PartialOrder.rel_trans (iInf_le _ ⟨hp⟩) (Spec.failure_OptionT post epost).le_wp)

end guard

/-! ## `List.mapM` -/

section mapM

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type w'} {β : Type u}

/-- `List.mapM` with a loop invariant over the elements consumed so far, the elements remaining,
and the outputs so far; each step maps one element and appends its output. -/
@[spec]
theorem Spec.mapM_list {xs : List α} {f : α → m β} (inv : Invariant α (List β) Pred)
    {epost : EPred}
    (step : ∀ pref cur suff bs, xs = pref ++ cur :: suff →
      ⦃ inv pref (cur :: suff) bs ⦄ f cur
        ⦃ fun b => inv (pref ++ [cur]) suff (bs ++ [b]); epost ⦄) :
    ⦃ inv [] xs [] ⦄ xs.mapM f ⦃ fun bs => inv xs [] bs; epost ⦄ := by
  suffices h : ∀ pref suff bs, xs = pref ++ suff →
      ⦃ inv pref suff bs ⦄ suff.mapM f ⦃ fun bs' => inv xs [] (bs ++ bs'); epost ⦄ by
    simpa using h [] xs [] rfl
  intro pref suff
  induction suff generalizing pref with
  | nil =>
    intro bs hxs
    simp only [List.mapM_nil]
    refine Triple.pure _ ?_
    simp only [List.append_nil] at hxs
    subst hxs
    simp only [List.append_nil]
    exact PartialOrder.rel_refl
  | cons x suff ih =>
    intro bs hxs
    simp only [List.mapM_cons]
    refine Triple.bind (f x) _ (fun b => inv (pref ++ [x]) suff (bs ++ [b]))
      (step pref x suff bs hxs) fun b => ?_
    refine Triple.bind (suff.mapM f) _ (fun bs' => inv xs [] (bs ++ [b] ++ bs'))
      (ih (pref ++ [x]) (bs ++ [b]) (by simp [hxs])) fun bs' => ?_
    refine Triple.pure _ ?_
    simp only [List.append_assoc, List.singleton_append]
    exact PartialOrder.rel_refl

end mapM

/-! ## Sequencing -/

section seq

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α β : Type u}

/-- `x <* y` runs both and keeps the first value. -/
@[spec]
theorem Spec.seqLeft (x : m α) (y : m β) (post : α → Pred) {epost : EPred} :
    ⦃ wp x (fun a => wp y (fun _ => post a) epost) epost ⦄ (x <* y) ⦃ post; epost ⦄ :=
  ⟨by
    rw [seqLeft_eq]
    refine PartialOrder.rel_trans ?_ (Spec.seq (Function.const β <$> x) y).le_wp
    exact WPMonad.map_le_wp_map (Function.const β) x
      (fun f => wp y (fun a => post (f a)) epost) epost⟩

/-- `x *> y` runs both and keeps the second value. -/
@[spec]
theorem Spec.seqRight (x : m α) (y : m β) (post : β → Pred) {epost : EPred} :
    ⦃ wp x (fun _ => wp y post epost) epost ⦄ (x *> y) ⦃ post; epost ⦄ :=
  ⟨by
    rw [seqRight_eq]
    refine PartialOrder.rel_trans ?_ (Spec.seq (Function.const α id <$> x) y).le_wp
    exact WPMonad.map_le_wp_map (Function.const α id) x
      (fun f => wp y (fun a => post (f a)) epost) epost⟩

end seq

end Std.WP

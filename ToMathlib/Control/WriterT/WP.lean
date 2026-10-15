/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.WriterT.WP
public import ToMathlib.Control.WriterT

/-!
# Append-based writer logs as weakest preconditions

`open scoped WriterT.AppendWP` interprets `WriterT ω m` whose log is combined by `++` from `∅`
(`LawfulAppend ω`, such as a list) through PolyFun's `WriterT.wpMonadOf`: the postcondition is
told the log accumulated so far. The scope also registers the `vcgen` rules for `tell` and for a
lifted base computation. PolyFun's `WriterT.MonoidWP` is the counterpart for monoid logs.
-/

public section

open Std.WP

namespace WriterT.AppendWP

universe u v w z

variable {m : Type u → Type v} {ω : Type u} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [EmptyCollection ω] [Append ω] [LawfulAppend ω]
  [Monad m] [WPMonad m Pred EPred]

/-- Opt-in `Std.WP` interpretation of a writer whose log is combined by `++` with unit `∅`, such
as a list: the postcondition is told the log accumulated so far. -/
scoped instance instWPMonad : WPMonad (WriterT ω m) (ω → Pred) EPred :=
  WriterT.wpMonadOf ∅ (· ++ ·) LawfulAppend.append_empty
    fun a b c => (LawfulAppend.append_assoc a b c).symm

/-- Writing to an append-based log extends the accumulated log on the right. -/
@[spec]
theorem Spec.tell (out : ω) (post : PUnit → ω → Pred) {epost : EPred} :
    Triple (MonadWriter.tell out : WriterT ω m PUnit) (fun w => post ⟨⟩ (w ++ out)) post
      epost :=
  ⟨WriterT.le_wp_tell_of (· ++ ·) out post epost⟩

/-- A lifted base computation leaves an append-based log unchanged. -/
@[spec]
theorem Spec.monadLift {α : Type u} (x : m α) (post : α → ω → Pred) {epost : EPred} :
    Triple (MonadLift.monadLift x : WriterT ω m α)
      (fun w => wp x (fun a => post a w) epost) post epost :=
  ⟨WriterT.le_wp_liftTell_of ∅ (· ++ ·) LawfulAppend.append_empty x post epost⟩

end WriterT.AppendWP

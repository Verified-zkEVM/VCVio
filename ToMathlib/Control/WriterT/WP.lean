/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Control.Do.Spec
public import ToMathlib.Control.WriterT

/-!
# Append-based writer logs as weakest preconditions

`open scoped WriterT.AppendWP` interprets `WriterT ω m` whose log is combined by `++` from `∅`
(`LawfulAppend ω`, such as a list) through PolyFun's `WriterT.wpMonadOf`: the postcondition is
told the log accumulated so far. The `vcgen` rules for `tell` and a lifted base computation
allow independent universes for the normal and exceptional assertion carriers.
PolyFun's `WriterT.MonoidWP` is the counterpart for monoid logs.
-/

public section

open Std.WP

namespace WriterT.AppendWP

universe u v w z

variable {m : Type u → Type v} {ω : Type u} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [EmptyCollection ω] [Append ω] [LawfulAppend ω]
  [Monad m] [WPMonad m Pred EPred]

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
